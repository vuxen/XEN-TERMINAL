import html
import tempfile
import asyncio
import json
import subprocess
import os
import uuid
import re
import urllib.request
import urllib.parse
import urllib.error
import threading

import numpy as np
import soundcard as sc

from bisect import bisect_right
from difflib import SequenceMatcher

from rich.markup import escape
from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll
from textual.widgets import Header, Footer, Input, Static, ListView, ListItem, Button


# Keep a reference to the MPV child process so Windows can stop it
# even when the terminal window is closed directly with its X button.
_ACTIVE_MPV_PROCESS = None
_WINDOWS_CONSOLE_HANDLER = None


def _terminate_active_mpv():
    global _ACTIVE_MPV_PROCESS

    process = _ACTIVE_MPV_PROCESS
    if process is None:
        return

    try:
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=1.5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=1.0)
    except (OSError, subprocess.SubprocessError):
        try:
            process.kill()
        except OSError:
            pass

    if _ACTIVE_MPV_PROCESS is process:
        _ACTIVE_MPV_PROCESS = None


def _install_windows_console_handler():
    """Stop MPV when the Windows console closes, logs off, or shuts down."""
    global _WINDOWS_CONSOLE_HANDLER

    if os.name != "nt":
        return

    import ctypes

    handler_type = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_uint)

    def handle_console_event(event):
        # CTRL_C_EVENT=0, CTRL_BREAK_EVENT=1, CTRL_CLOSE_EVENT=2,
        # CTRL_LOGOFF_EVENT=5, CTRL_SHUTDOWN_EVENT=6.
        if event in (0, 1, 2, 5, 6):
            _terminate_active_mpv()

        # Let Python/Textual handle Ctrl+C and Ctrl+Break normally.
        # For close/logoff/shutdown, report the event as handled.
        return event in (2, 5, 6)

    _WINDOWS_CONSOLE_HANDLER = handler_type(handle_console_event)
    ctypes.windll.kernel32.SetConsoleCtrlHandler(
        _WINDOWS_CONSOLE_HANDLER, True
    )


class AudioLoopbackMonitor:
    """Captures Windows speaker loopback and converts it into equalizer levels."""

    # More frequency bands create a longer, finer visualizer.
    BAR_COUNT = 96
    SAMPLE_RATE = 22050
    BLOCK_SIZE = 4096

    def __init__(self):
        self._stop_event = threading.Event()
        self._thread = None
        self._lock = threading.Lock()
        self._levels = [0.0] * self.BAR_COUNT
        self.error = None

    def start(self):
        self.stop()
        self.error = None
        self._stop_event.clear()
        self._thread = threading.Thread(
            target=self._capture_loop,
            name="ytmusic-audio-loopback",
            daemon=True,
        )
        self._thread.start()

    def stop(self):
        self._stop_event.set()
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=1.0)
        self._thread = None
        with self._lock:
            self._levels = [0.0] * self.BAR_COUNT

    def get_levels(self):
        with self._lock:
            return list(self._levels)

    
    def _capture_loop(self):
        try:
            speaker = sc.default_speaker()

            if speaker is None:
                raise RuntimeError("Windows default speaker was not found.")

            loopback = sc.get_microphone(
                id=str(speaker.name),
                include_loopback=True,
            )

            with loopback.recorder(
                samplerate=self.SAMPLE_RATE,
                channels=2,
                blocksize=self.BLOCK_SIZE,
            ) as recorder:

                frequencies = np.fft.rfftfreq(
                    self.BLOCK_SIZE,
                    d=1 / self.SAMPLE_RATE,
                )

                edges = np.geomspace(
                    45,
                    10000,
                    self.BAR_COUNT + 1,
                )

                while not self._stop_event.is_set():

                    samples = recorder.record(
                        numframes=self.BLOCK_SIZE
                    )

                    if samples is None or len(samples) == 0:
                        continue

                    mono = np.mean(samples, axis=1)
                    mono = mono - np.mean(mono)

                    window = np.hanning(len(mono))

                    spectrum = np.abs(
                        np.fft.rfft(mono * window)
                    ) / max(np.sum(window) / 2, 1e-9)

                    fresh_levels = []

                    for index in range(self.BAR_COUNT):

                        mask = (
                            (frequencies >= edges[index])
                            & (frequencies < edges[index + 1])
                        )

                        band = spectrum[mask]

                        # Keep narrow low-frequency bands responsive even when
                        # an FFT band contains no exact frequency bin.
                        if band.size:
                            strength = float(
                                np.sqrt(np.mean(np.square(band)))
                            )
                        else:
                            nearest_bin = int(
                                np.argmin(np.abs(frequencies - edges[index]))
                            )
                            strength = float(spectrum[nearest_bin])

                        db = 20 * np.log10(strength + 1e-8)

                        level = np.clip(
                            (db + 75) / 40,
                            0.0,
                            1.0,
                        )

                        level = float(level ** 0.8)

                        fresh_levels.append(level)

                    with self._lock:

                        self._levels = [
                            old * (0.58 if fresh > old else 0.86)
                            + fresh * (0.42 if fresh > old else 0.14)
                            for old, fresh in zip(
                                self._levels,
                                fresh_levels,
                            )
                        ]

        except Exception as error:
            self.error = str(error)


class YTMusicApp(App):

    TITLE = "YTMusic Terminal Player"
    SUB_TITLE = "Your Personal Music Player"

    CSS = """
    Screen {
        background: #101014;
    }

    #main {
        height: 1fr;
        padding: 1 2;
    }

    #sidebar {
        width: 30%;
        border: round #44445a;
        padding: 1;
    }

    #content {
        width: 70%;
        border: round #44445a;
        padding: 1 2;
    }

    #search-row {
        height: 3;
        width: 100%;
        margin-bottom: 1;
    }

    #search {
        width: 1fr;
    }

    #clear-search {
        width: 5;
        min-width: 5;
        margin-left: 1;
        padding: 0;
    }

    #results {
        height: 1fr;
        border: none;
    }

    ListItem {
        padding: 1;
        height: auto;
    }

    ListItem.--highlight {
        background: #303044;
    }

    #details {
        height: 11;
        color: #b8b8cc;
    }

    #visualizer {
        height: 7;
        color: #b8b8cc;
        content-align: center middle;
        padding: 0 1;
    }

    #lyrics_scroll {
        height: 1fr;
        border: none;
        scrollbar-color: #555570;
    }

    #lyrics {
        padding: 1;
        color: #b8b8cc;
    }
    """

    BINDINGS = [
        ("ctrl+q", "quit", "Quit"),
        ("q", "quit", "Quit"),
        ("space", "toggle_pause", "Pause / Resume"),
        ("n", "next_song", "Next"),
        ("p", "previous_song", "Previous"),
        ("s", "stop_music", "Stop"),
        ("r", "toggle_repeat", "Repeat ON / OFF"),
    ]

    def __init__(self):
        super().__init__()

        self.tracks = []
        self.current_index = None

        self.player = None
        self.mpv_pipe = None

        self.is_paused = False
        self.repeat_enabled = False
        self.audio_monitor = AudioLoopbackMonitor()

        self.current_title = "No song selected"
        self.current_artist = "Unknown Artist"

        self.playback_position = 0
        self.playback_duration = 0

        self.lyrics_lines = []
        self.plain_lyrics = []
        self.lyrics_mode = None
        self.lyrics_status = "idle"

        self.lyrics_task = None
        self.lyrics_request_id = 0
        self.search_request_id = 0

    def compose(self) -> ComposeResult:

        yield Header()

        with Horizontal(id="main"):

            with Vertical(id="sidebar"):

                yield Static("[bold cyan]YT MUSIC[/bold cyan]")

                with Horizontal(id="search-row"):
                    yield Input(
                        placeholder="Search songs or artists...",
                        id="search"
                    )
                    yield Button("X", id="clear-search", tooltip="Clear search")

                yield ListView(id="results")

            with Vertical(id="content"):

                yield Static(
                    "[bold cyan]WELCOME TO YTMUSIC[/bold cyan]\n\n"
                    "Search and select a song to start playback.",
                    id="details"
                )

                yield Static(
                    "",
                    id="visualizer"
                )

                with VerticalScroll(id="lyrics_scroll"):

                    yield Static(
                        "",
                        id="lyrics"
                    )

        yield Footer()

    def on_mount(self):

        self.set_interval(0.25, self.refresh_playback_info)
        self.set_interval(0.05, self.refresh_visualizer)

    async def on_input_submitted(self, event: Input.Submitted):

        query = event.value.strip()

        if not query:
            return

        self.search_request_id += 1
        search_request_id = self.search_request_id

        results_panel = self.query_one("#results", ListView)
        details_panel = self.query_one("#details", Static)

        await results_panel.clear()

        self.tracks = []
        self.current_index = None

        await results_panel.append(
            ListItem(
                Static("[yellow]Searching YouTube...[/yellow]")
            )
        )

        details_panel.update(
            "[bold cyan]YOUTUBE SEARCH[/bold cyan]\n\n"
            f"Query: {escape(query)}\n\n"
            "Searching for music..."
        )

        try:

            tracks = await asyncio.to_thread(
                self.search_youtube, query
            )

            if search_request_id != self.search_request_id:
                return

            await results_panel.clear()

            self.tracks = tracks

            if not tracks:

                await results_panel.append(
                    ListItem(
                        Static("[red]No songs found.[/red]")
                    )
                )

                return

            for number, track in enumerate(tracks, start=1):

                title = escape(
                    track.get("title", "Unknown Title")
                )

                artist = escape(
                    track.get("channel")
                    or track.get("uploader")
                    or "Unknown Artist"
                )

                await results_panel.append(
                    ListItem(
                        Static(
                            f"[bold yellow]{number}.[/bold yellow] "
                            f"[bold]{title}[/bold]\n"
                            f"[dim]{artist}[/dim]"
                        )
                    )
                )

            details_panel.update(
                "[bold green]SEARCH COMPLETE[/bold green]\n\n"
                f"Query: {escape(query)}\n\n"
                f"Found {len(tracks)} songs.\n\n"
                "[bold cyan]PLAYBACK CONTROLS[/bold cyan]\n\n"
                "SPACE = Pause / Resume\n"
                "N = Next Song\n"
                "P = Previous Song\n"
                "S = Stop Playback\n"
                "Q = Quit"
            )

            results_panel.focus()

        except Exception as error:

            if search_request_id != self.search_request_id:
                return

            await results_panel.clear()

            await results_panel.append(
                ListItem(
                    Static(
                        f"[red]Error: {escape(str(error))}[/red]"
                    )
                )
            )

    async def on_button_pressed(self, event: Button.Pressed):

        if event.button.id != "clear-search":
            return

        # Invalidate an in-progress search so old results do not return.
        self.search_request_id += 1

        search_input = self.query_one("#search", Input)
        search_input.value = ""

        results_panel = self.query_one("#results", ListView)
        await results_panel.clear()

        # Clear the visible search playlist without stopping the current song.
        self.tracks = []
        self.current_index = None

        # Invalidate and cancel pending lyrics retrieval for the current display.
        self.lyrics_request_id += 1
        if self.lyrics_task and not self.lyrics_task.done():
            self.lyrics_task.cancel()
        self.lyrics_task = None

        self.lyrics_lines = []
        self.plain_lyrics = []
        self.lyrics_mode = None
        self.lyrics_status = "idle"
        self.update_lyrics("")

        # Keep the current playback and its dashboard running.
        if not self.player or self.player.poll() is not None:
            self.update_details(
                "[bold cyan]WELCOME TO YTMUSIC[/bold cyan]\n\n"
                "Search and select a song to start playback."
            )

        search_input.focus()

    async def on_list_view_selected(self, event: ListView.Selected):

        index = event.list_view.index

        if index is None or index >= len(self.tracks):
            return

        self.play_track(index)

    def play_track(self, index):

        if index < 0 or index >= len(self.tracks):
            return

        track = self.tracks[index]

        title = track.get("title", "Unknown Title")

        artist = (
            track.get("channel")
            or track.get("uploader")
            or "Unknown Artist"
        )

        video_id = track.get("id")

        if not video_id:

            self.update_details(
                "[red]Unable to play this song.[/red]"
            )

            return

        url = f"https://www.youtube.com/watch?v={video_id}"

        self.stop_player()

        self.current_title = title
        self.current_artist = artist

        self.current_index = index

        self.playback_position = 0
        self.playback_duration = 0

        self.is_paused = False

        self.lyrics_lines = []
        self.plain_lyrics = []
        self.lyrics_mode = None
        self.lyrics_status = "loading"

        self.lyrics_request_id += 1

        request_id = self.lyrics_request_id

        self.mpv_pipe = (
            rf"\\.\pipe\ytmusic-mpv-{os.getpid()}-{uuid.uuid4().hex}"
        )

        command = [
            "mpv",
            "--no-video",
            "--force-window=no",
            "--no-terminal",
            "--really-quiet",
            "--ytdl-format=bestaudio/best",
            f"--input-ipc-server={self.mpv_pipe}",
            url
        ]

        try:

            options = {}

            if os.name == "nt":

                options["creationflags"] = (
                    subprocess.CREATE_NO_WINDOW
                )

            self.player = subprocess.Popen(
                command,
                **options
            )

            global _ACTIVE_MPV_PROCESS
            _ACTIVE_MPV_PROCESS = self.player

            self.audio_monitor.start()

            self.update_details(
                self.build_dashboard()
            )

            self.update_lyrics(
                "[yellow]Searching for lyrics...[/yellow]"
            )

            self.lyrics_task = asyncio.create_task(
                self.load_lyrics(
                    request_id,
                    title,
                    artist,
                    track.get("duration"),
                    video_id
                )
            )

        except FileNotFoundError:

            self.player = None

            self.update_details(
                "[red]MPV was not found.[/red]\n"
                "Check your MPV installation."
            )

        except Exception as error:

            self.player = None

            self.update_details(
                f"[red]Playback error:[/red]\n"
                f"{escape(str(error))}"
            )

    # ---------------------------------
    # MPV PLAYBACK CONTROL
    # ---------------------------------

    def send_mpv_command(self, command):

        if not self.player or self.player.poll() is not None:
            return False

        if not self.mpv_pipe:
            return False

        message = json.dumps({
            "command": command
        }) + "\n"

        try:

            with open(
                self.mpv_pipe,
                "w",
                encoding="utf-8"
            ) as pipe:

                pipe.write(message)
                pipe.flush()

            return True

        except (OSError, IOError):

            return False

    def get_playback_info(self):

        if not self.player or self.player.poll() is not None:
            return None

        if not self.mpv_pipe:
            return None

        requests = {
            "position": ["get_property", "time-pos"],
            "duration": ["get_property", "duration"]
        }

        responses = {}

        try:

            with open(
                self.mpv_pipe,
                "r+",
                encoding="utf-8",
                buffering=1
            ) as pipe:

                for request_id, command in enumerate(
                    requests.values(), start=1
                ):

                    pipe.write(json.dumps({
                        "command": command,
                        "request_id": request_id
                    }) + "\n")

                for _ in range(2):

                    line = pipe.readline()

                    if not line:
                        break

                    response = json.loads(line)

                    request_id = response.get("request_id")

                    if request_id == 1:

                        responses["position"] = (
                            response.get("data")
                        )

                    elif request_id == 2:

                        responses["duration"] = (
                            response.get("data")
                        )

            return responses

        except (OSError, IOError, json.JSONDecodeError):

            return None

    async def refresh_playback_info(self):

        if not self.player:
            return

        if self.player.poll() is not None:

            global _ACTIVE_MPV_PROCESS
            if _ACTIVE_MPV_PROCESS is self.player:
                _ACTIVE_MPV_PROCESS = None

            self.player = None
            self.mpv_pipe = None
            self.is_paused = False
            self.audio_monitor.stop()

            # Continue through the playlist automatically.
            if self.current_index is not None and self.tracks:
                next_index = self.current_index + 1

                if next_index < len(self.tracks):
                    self.play_track(next_index)
                    return

                if self.repeat_enabled:
                    self.play_track(0)
                    return

            self.update_details(
                self.build_dashboard()
                + "\n\n[bold yellow]PLAYLIST FINISHED[/bold yellow]"
            )
            self.update_visualizer()
            return

        info = await asyncio.to_thread(
            self.get_playback_info
        )

        if info:

            position = info.get("position")
            duration = info.get("duration")

            if isinstance(position, (int, float)):

                self.playback_position = position

            if isinstance(duration, (int, float)):

                self.playback_duration = duration

        self.update_details(
            self.build_dashboard()
        )

        self.refresh_lyrics_display()

    # ---------------------------------
    # MUSIC INFORMATION
    # ---------------------------------

    @staticmethod
    def format_time(seconds):

        if seconds is None:
            return "--:--"

        seconds = max(0, int(seconds))

        minutes, seconds = divmod(seconds, 60)

        hours, minutes = divmod(minutes, 60)

        if hours:

            return f"{hours}:{minutes:02}:{seconds:02}"

        return f"{minutes:02}:{seconds:02}"

    def build_dashboard(self):

        position = self.playback_position
        duration = self.playback_duration

        if self.is_paused:
            status = "[bold yellow]PAUSED[/bold yellow]"
        elif self.player and self.player.poll() is None:
            status = "[bold green]PLAYING[/bold green]"
        else:
            status = "[bold red]STOPPED[/bold red]"

        if duration > 0:
            progress = min(position / duration, 1)
            percentage = int(progress * 100)
            filled = int(progress * 30)
            bar = (
                "[cyan]" + "━" * filled + "[/cyan]"
                + "[dim]" + "─" * (30 - filled) + "[/dim]"
            )
        else:
            percentage = 0
            bar = "[dim]" + "─" * 30 + "[/dim]"

        repeat_status = (
            "[bold green]ON[/bold green]"
            if self.repeat_enabled
            else "[dim]OFF[/dim]"
        )

        return (
            "[bold cyan]NOW PLAYING[/bold cyan]\n"
            f"[bold white]{escape(self.current_title)}[/bold white]\n"
            f"[dim]{escape(self.current_artist)}[/dim]\n\n"
            f"Status: {status}    Repeat: {repeat_status}\n"
            f"[bold]{self.format_time(position)}[/bold]"
            f" / {self.format_time(duration)}\n"
            f"{bar}  [dim]{percentage}%[/dim]\n"
            "[dim]SPACE Pause  N Next  P Previous  S Stop  R Repeat[/dim]"
        )

    # ---------------------------------
    # LRCLIB LYRICS INTEGRATION
    # ---------------------------------

    @staticmethod
    def fetch_url(url):

        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": "YTMusicTerminalPlayer/1.0"
            }
        )

        with urllib.request.urlopen(
            request,
            timeout=20
        ) as response:

            return json.loads(
                response.read().decode("utf-8")
            )

    @staticmethod
    def normalize_text(value):
        """Normalize text while preserving Unicode letters and numbers."""
        value = unicodedata.normalize("NFKC", str(value)).casefold()

        return re.sub(
            r"[^\\w]+",
            "",
            value,
            flags=re.UNICODE
        )

    @classmethod
    def fetch_lyrics(cls, title, artist, duration=None):

        base_url = "https://lrclib.net/api/get"

        params = {
            "track_name": title,
            "artist_name": artist
        }

        if isinstance(duration, (int, float)):
            if 1 <= duration <= 3600:
                params["duration"] = int(duration)

        url = (
            base_url
            + "?"
            + urllib.parse.urlencode(params)
        )

        try:
            return cls.fetch_url(url)

        except urllib.error.HTTPError as error:
            if error.code != 404:
                raise

        # Remove common YouTube title labels.

        clean_title = re.sub(
            r"\s*[\(\[\-]\s*(official music video|official video|official audio|lyrics|lyric video|audio|hd|4k)[^\)\]]*[\)\]]?\s*",
            " ",
            title,
            flags=re.IGNORECASE
        ).strip()

        clean_title = re.sub(
            r"\s+",
            " ",
            clean_title
        ).strip()

        # Search using the cleaned title only.
        # YouTube channel names often differ from the real artist.

        search_url = (
            "https://lrclib.net/api/search?"
            + urllib.parse.urlencode({
                "track_name": clean_title
            })
        )

        results = cls.fetch_url(search_url)

        if not isinstance(results, list) or not results:
            return None

        wanted_title = cls.normalize_text(clean_title)
        wanted_artist = cls.normalize_text(artist)

        best_result = None
        best_score = 0

        for result in results:

            result_title = cls.normalize_text(
                result.get("trackName", "")
            )

            result_artist = cls.normalize_text(
                result.get("artistName", "")
            )

            title_score = SequenceMatcher(
                None,
                wanted_title,
                result_title
            ).ratio()

            artist_score = SequenceMatcher(
                None,
                wanted_artist,
                result_artist
            ).ratio()

            score = (
                title_score * 0.85
                + artist_score * 0.15
            )

            if score > best_score:
                best_score = score
                best_result = result

        if best_score < 0.65:
            return None

        return best_result

    @staticmethod
    def fetch_youtube_captions(video_id):
        """Download and parse available YouTube subtitle/caption tracks."""
        if not video_id:
            return None

        url = f"https://www.youtube.com/watch?v={video_id}"

        with tempfile.TemporaryDirectory() as temp_dir:
            output_template = os.path.join(temp_dir, "%(id)s.%(ext)s")

            command = [
                "yt-dlp",
                "--skip-download",
                "--write-subs",
                "--write-auto-subs",
                "--sub-langs", "all",
                "--sub-format", "vtt/best",
                "--no-warnings",
                "--no-playlist",
                "-o", output_template,
                url,
            ]

            try:
                subprocess.run(
                    command,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=45,
                    check=False,
                )
            except (FileNotFoundError, subprocess.TimeoutExpired):
                return None

            subtitle_files = [
                os.path.join(temp_dir, filename)
                for filename in os.listdir(temp_dir)
                if filename.lower().endswith(".vtt")
            ]

            best_lines = []

            for subtitle_file in subtitle_files:
                try:
                    with open(subtitle_file, "r", encoding="utf-8-sig") as file:
                        content = file.read()
                except OSError:
                    continue

                lines = []
                previous_text = None

                for block in re.split(r"\n\s*\n", content):
                    timestamp = re.search(
                        r"(?m)^(\d{1,2}:)?\d{2}:\d{2}\.\d+\s*-->",
                        block,
                    )
                    if not timestamp:
                        continue

                    time_text = block[:block.find("-->")].strip()
                    parts = time_text.split(":")

                    try:
                        if len(parts) == 3:
                            seconds = (
                                int(parts[0]) * 3600
                                + int(parts[1]) * 60
                                + float(parts[2])
                            )
                        elif len(parts) == 2:
                            seconds = int(parts[0]) * 60 + float(parts[1])
                        else:
                            continue
                    except (ValueError, IndexError):
                        continue

                    cue_text = block[block.find("-->") + 3:]
                    cue_text = re.sub(r"(?m)^\s*\d+\s*$", "", cue_text)
                    cue_text = re.sub(r"<[^>]+>", "", cue_text)
                    cue_text = html.unescape(cue_text)
                    cue_text = re.sub(r"\s+", " ", cue_text).strip()

                    if not cue_text or cue_text == previous_text:
                        continue

                    previous_text = cue_text
                    lines.append((seconds, cue_text))

                if len(lines) > len(best_lines):
                    best_lines = lines

            return best_lines or None

    async def load_lyrics(
        self,
        request_id,
        title,
        artist,
        duration,
        video_id,
    ):
        try:
            data = await asyncio.to_thread(
                self.fetch_lyrics,
                title,
                artist,
                duration,
            )

            if request_id != self.lyrics_request_id:
                return

            synced = data.get("syncedLyrics") if data else None
            plain = data.get("plainLyrics") if data else None

            # First choice: synchronized LRCLIB lyrics.
            if synced:
                parsed = self.parse_synced_lyrics(synced)
                if parsed:
                    self.lyrics_lines = parsed
                    self.lyrics_mode = "synced"
                    self.lyrics_status = "loaded"
                    self.refresh_lyrics_display()
                    return

            # Second choice: captions available on the YouTube video.
            captions = await asyncio.to_thread(
                self.fetch_youtube_captions,
                video_id,
            )

            if request_id != self.lyrics_request_id:
                return

            if captions:
                self.lyrics_lines = captions
                self.lyrics_mode = "synced"
                self.lyrics_status = "loaded"
                self.refresh_lyrics_display()
                return

            # Last choice: plain LRCLIB lyrics.
            if plain:
                self.plain_lyrics = plain.splitlines()
                self.lyrics_mode = "plain"
                self.lyrics_status = "loaded"
                self.refresh_lyrics_display()
                return

            self.lyrics_status = "not_found"
            self.update_lyrics(
                "[yellow]No lyrics or captions found for this video.[/yellow]\n\n"
                "This video has no matching LRCLIB lyrics or readable YouTube captions."
            )

        except Exception as error:
            if request_id != self.lyrics_request_id:
                return

            self.lyrics_status = "error"
            self.update_lyrics(
                "[red]Unable to retrieve lyrics.[/red]\n\n"
                f"[dim]{escape(str(error))}[/dim]"
            )

    # ---------------------------------
    # SYNCHRONIZED LYRICS
    # ---------------------------------

    @staticmethod
    def parse_synced_lyrics(text):

        lines = []

        pattern = re.compile(
            r"\[(\d{1,2}):(\d{2})(?:[.:](\d{1,3}))?\]"
        )

        for raw_line in text.splitlines():

            matches = list(pattern.finditer(raw_line))

            if not matches:
                continue

            lyric_text = pattern.sub(
                "",
                raw_line
            ).strip()

            if not lyric_text:
                continue

            for match in matches:

                minutes = int(match.group(1))

                seconds = int(match.group(2))

                fraction = match.group(3) or "0"

                fraction_value = (
                    int(fraction)
                    / (10 ** len(fraction))
                )

                timestamp = (
                    minutes * 60
                    + seconds
                    + fraction_value
                )

                lines.append((
                    timestamp,
                    lyric_text
                ))

        lines.sort(key=lambda item: item[0])

        return lines

    def refresh_lyrics_display(self):

        if self.lyrics_status != "loaded":
            return

        if self.lyrics_mode == "plain":
            output = "\n".join(
                escape(line)
                for line in self.plain_lyrics
            )
            self.update_lyrics(
                output or "[dim]No lyrics available.[/dim]"
            )
            return

        if self.lyrics_mode == "synced":
            if not self.lyrics_lines:
                return

            timestamps = [line[0] for line in self.lyrics_lines]
            current_index = bisect_right(
                timestamps,
                self.playback_position
            ) - 1
            current_index = max(0, current_index)

            output = []
            start = max(0, current_index - 2)
            end = min(len(self.lyrics_lines), current_index + 3)

            for index in range(start, end):
                lyric_text = self.lyrics_lines[index][1]

                if index == current_index:
                    line_start = self.lyrics_lines[index][0]
                    if index + 1 < len(self.lyrics_lines):
                        line_end = self.lyrics_lines[index + 1][0]
                    else:
                        line_end = line_start + 4.0

                    interval = max(1.2, min(8.0, line_end - line_start))
                    progress = min(
                        0.999,
                        max(0.0, (self.playback_position - line_start) / interval)
                    )
                    words = re.findall(r"\S+", lyric_text)
                    if not words:
                        output.append("[bold cyan]♪ ♪[/bold cyan]")
                        continue

                    active_word = min(
                        len(words) - 1,
                        int(progress * len(words))
                    )

                    rendered_words = []
                    for word_index, word in enumerate(words):
                        safe_word = escape(word)
                        if word_index < active_word:
                            rendered_words.append(
                                f"[bold #55aaff]{safe_word}[/bold #55aaff]"
                            )
                        elif word_index == active_word:
                            rendered_words.append(
                                f"[bold #ffffff on #2456a6]{safe_word}[/bold #ffffff on #2456a6]"
                            )
                        else:
                            rendered_words.append(f"[dim]{safe_word}[/dim]")

                    output.append(
                        "[bold cyan]♪ [/bold cyan]"
                        + " ".join(rendered_words)
                        + "[bold cyan] ♪[/bold cyan]"
                    )
                elif index < current_index:
                    output.append(f"[dim]{escape(lyric_text)}[/dim]")
                else:
                    output.append(f"[#77778f]{escape(lyric_text)}[/#77778f]")

            self.update_lyrics("\n\n".join(output))

    def update_lyrics(self, message):

        self.query_one("#lyrics", Static).update(message)

    def refresh_visualizer(self):

        if not self.player or self.player.poll() is not None:
            return

        self.update_visualizer()

    def update_visualizer(self):

        panel = self.query_one("#visualizer", Static)
        source_levels = self.audio_monitor.get_levels()

        # Fit the bars to the current panel width. Textual updates panel.size
        # after a terminal resize, so the visualizer redraws at the new width.
        bar_count = max(1, panel.size.width - 2)
        if source_levels:
            positions = np.linspace(0, len(source_levels) - 1, bar_count)
            levels = np.interp(
                positions,
                np.arange(len(source_levels)),
                source_levels,
            )
        else:
            levels = np.zeros(bar_count, dtype=float)

        rows = 6
        rendered_rows = []

        for row in range(rows, 0, -1):
            pieces = []
            for level in levels:
                height = int(round(float(level) * rows))

                if height >= row:
                    intensity = row / rows
                    if intensity <= 0.50:
                        color = "#a9b99f"  # soft green
                    elif intensity <= 0.78:
                        color = "#f2c45b"  # yellow
                    elif intensity <= 0.92:
                        color = "#f28b45"  # orange
                    else:
                        color = "#ed5b58"  # red
                    pieces.append(f"[{color}]┃[/{color}]")
                else:
                    pieces.append(" ")

            rendered_rows.append("".join(pieces))

        if self.audio_monitor.error:
            footer = "[dim]Audio loopback unavailable. Check Windows output device.[/dim]"
        elif not self.player or self.player.poll() is not None:
            footer = "[dim]Waiting for music...[/dim]"
        else:
            footer = "[dim]LIVE AUDIO  •  REAL-TIME LOOPBACK[/dim]"

        panel.update("\n".join(rendered_rows) + "\n" + footer)

    # ---------------------------------
    # PLAYBACK SHORTCUTS
    # ---------------------------------

    def action_toggle_pause(self):

        if not self.player or self.player.poll() is not None:
            return

        if self.send_mpv_command(["cycle", "pause"]):

            self.is_paused = not self.is_paused

            self.update_details(
                self.build_dashboard()
            )

    def action_toggle_repeat(self):

        self.repeat_enabled = not self.repeat_enabled
        self.update_details(self.build_dashboard())

    def stop_player(self):

        global _ACTIVE_MPV_PROCESS

        self.audio_monitor.stop()

        if self.lyrics_task:

            if not self.lyrics_task.done():

                self.lyrics_task.cancel()

            self.lyrics_task = None

        if self.player and self.player.poll() is None:

            self.player.terminate()

            try:

                self.player.wait(timeout=2)

            except subprocess.TimeoutExpired:

                self.player.kill()
                self.player.wait()

        if _ACTIVE_MPV_PROCESS is self.player:
            _ACTIVE_MPV_PROCESS = None

        self.player = None
        self.mpv_pipe = None

        self.is_paused = False

        self.playback_position = 0
        self.playback_duration = 0

    def action_next_song(self):

        if not self.tracks:
            return

        if self.current_index is None:

            next_index = 0

        else:

            next_index = self.current_index + 1

            if next_index >= len(self.tracks):
                if self.repeat_enabled:
                    next_index = 0
                else:
                    return

        self.play_track(next_index)

    def action_previous_song(self):

        if not self.tracks:
            return

        if self.current_index is None:

            previous_index = 0

        else:

            previous_index = self.current_index - 1

            if previous_index < 0:
                if self.repeat_enabled:
                    previous_index = len(self.tracks) - 1
                else:
                    previous_index = 0

        self.play_track(previous_index)

    def action_stop_music(self):

        self.stop_player()

        self.lyrics_status = "idle"
        self.lyrics_mode = None

        self.update_details(
            "[bold yellow]PLAYBACK STOPPED[/bold yellow]\n\n"
            "Select another song to play."
        )

        self.update_lyrics("")
        self.query_one("#visualizer", Static).update("")

    def update_details(self, message):

        self.query_one("#details", Static).update(message)

    def on_unmount(self):

        self.stop_player()

    # ---------------------------------
    # YOUTUBE SEARCH
    # ---------------------------------

    @staticmethod
    def search_youtube(query):

        command = [
            "yt-dlp",
            "--flat-playlist",
            "--dump-json",
            "--no-warnings",
            "--skip-download",
            f"ytsearch20:{query}"
        ]

        process = subprocess.run(
            command,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=60
        )

        if process.returncode != 0:

            raise RuntimeError(
                process.stderr.strip()
                or "YouTube search failed."
            )

        tracks = []

        excluded_words = [
            "live",
            "remix",
            "cover",
            "karaoke",
            "nightcore",
            "sped up",
            "slowed"
        ]

        for line in process.stdout.splitlines():

            if not line.strip():
                continue

            track = json.loads(line)

            title = track.get(
                "title", ""
            ).lower()

            if any(
                word in title
                for word in excluded_words
            ):
                continue

            tracks.append(track)

            if len(tracks) >= 10:
                break

        return tracks


if __name__ == "__main__":

    _install_windows_console_handler()
    YTMusicApp().run()
