"""
Study Music  — refactored with:
  • Shuffle / Loop-one / Loop-all
  • Cover art + playback controls moved into album header area
  • Wider queue panel, taller queue list
  • Narrower song list
  • Top-5 most-played sidebar section
  • Starred playlist view (click STARRED header to filter main list)
  • Album strip "Starred only" filter toggle
  • Transition animation on album card selection
  • Custom pomodoro interval input
  • Session-open timer with reset
  • To-do checkboxes  (- [ ] / - [x] syntax rendered as clickable rows)
  • Stats tab (session time, top plays, total tracks played)
  • System tray icon (pystray)  — right-click → Show / Quit
  • m3u export of queue

  m3u FORMAT NOTE
  ───────────────
  An .m3u file is a plain-text playlist understood by VLC, foobar2000,
  Windows Media Player, etc.  Each line is either a comment (#...) or
  an absolute/relative path to an audio file.  Extended m3u adds a
  header line  #EXTM3U  and per-track lines like:
      #EXTINF:duration,Artist - Title
      /path/to/file.mp3
  We write extended m3u so the queue can be round-tripped perfectly.

  Persistence files (same directory as the script):
    todo.txt            — raw to-do text
    favourites.txt      — absolute paths, one per line
    cover_choices.json  — remembered album cover index per album
    playcounts.json     — {absolute_path: int}  most-played tracking
    session_total.json  — {"seconds": int}  cumulative open time
"""

import os
import sys
import threading
import ctypes
import json
import time
import re

import customtkinter as ctk
import pygame
from PIL import Image, ImageDraw

# ── optional system tray ──────────────────────────────────────────────────────
try:
    import pystray
    from pystray import MenuItem as TrayItem
    HAS_TRAY = True
except ImportError:
    HAS_TRAY = False

# ── constants ─────────────────────────────────────────────────────────────────
AUDIO_EXTENSIONS = (".mp3", ".wav", ".ogg", ".flac")
TODO_FILE         = "todo.txt"
FAVOURITES_FILE   = "favourites.txt"
COVER_FILE        = "cover_choices.json"
PLAYCOUNTS_FILE   = "playcounts.json"
SESSION_FILE      = "session_total.json"

C_BG      = "#090b0f"
C_SURFACE = "#0f1117"
C_RAISED  = "#161b24"
C_HOVER   = "#1d2433"
C_BORDER  = "#232d3f"
C_ACCENT  = "#3d7ef5"
C_ACCH    = "#2d62cc"
C_ACCENT2 = "#6da0ff"
C_STAR    = "#f0b429"
C_RED     = "#c0394b"
C_REDH    = "#9e2a3a"
C_GREEN   = "#2ecc71"
C_TEXT    = "#d8e0ee"
C_MUTED   = "#45516a"
C_DIM     = "#1e2536"

FONT = "Segoe UI"

try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    try:
        ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass
APP_DIR = os.path.dirname(os.path.abspath(__file__))
os.chdir(APP_DIR)

def fmt_time(s: float) -> str:
    s = max(0, int(s))
    return f"{s // 60}:{s % 60:02d}"

def fmt_hms(s: int) -> str:
    h, rem = divmod(s, 3600)
    m, sec = divmod(rem, 60)
    if h:
        return f"{h}h {m:02d}m {sec:02d}s"
    return f"{m:02d}m {sec:02d}s"


# ═════════════════════════════════════════════════════════════════════════════
class StudyApp(ctk.CTk):

    # ── init ──────────────────────────────────────────────────────────────────
    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")

        self.title("Study Music")
        self.configure(fg_color=C_BG)
        self.attributes("-fullscreen", True)
        self.bind("<Escape>", lambda _e: self.close_app())
        self.bind("<F11>",    lambda _e: self.toggle_fullscreen())
        self.protocol("WM_DELETE_WINDOW", self.close_app)

        cwd = os.getcwd()
        self.music_dir   = os.path.join(cwd, "Music")
        self.todo_path   = os.path.join(cwd, TODO_FILE)
        self.favs_path   = os.path.join(cwd, FAVOURITES_FILE)
        self.cover_path  = os.path.join(cwd, COVER_FILE)
        self.plays_path  = os.path.join(cwd, PLAYCOUNTS_FILE)
        self.sess_path   = os.path.join(cwd, SESSION_FILE)

        # library
        self.selected_folder  = None
        self.albums           = []
        self.album_offset     = 0
        self.visible_albums   = 4
        self.cover_cache      = {}
        self.cover_indexes    = self._load_json(self.cover_path, {})
        self.songs            = []
        self.favourites       = self._load_lines(self.favs_path)
        self.queue            = []
        self.play_counts      = self._load_json(self.plays_path, {})

        # playback
        self.current_song    = None
        self.is_playing      = False
        self._song_length    = 0.0
        self._seek_offset    = 0.0
        self._seek_dragging  = False

        # shuffle / loop  ("none" | "one" | "all")
        self.shuffle_on   = False
        self._shuffle_history = []   # for back-navigation during shuffle
        self.loop_mode    = "none"   # none / one / all

        # starred-playlist mode
        self.starred_view = False    # True → main list shows only starred songs
        self.starred_album_filter = False  # True → album strip shows starred albums only

        # widget dicts
        self.song_btns  = {}
        self.star_btns  = {}
        self.queue_btns = {}
        self.fav_btns   = {}

        # scheduled callbacks
        self.timer_running  = False
        self.time_left      = 25 * 60
        self._timer_id      = None
        self._todo_save_id  = None
        self._track_id      = None
        self._seek_id       = None
        self._session_id    = None

        # session timer
        saved = self._load_json(self.sess_path, {"seconds": 0})
        self.session_seconds = saved.get("seconds", 0)
        self._open_start     = time.monotonic()

        # album animation
        self._anim_id    = None
        self._anim_col   = None   # column index being animated
        self._anim_step  = 0

        # popout
        self.popout       = None
        self._po_cover_img = None

        # tray
        self._tray_icon = None
        self._tray_visible = True   # main window visible

        try:
            pygame.mixer.init()
            pygame.mixer.music.set_volume(0.5)
            self.audio_ready = True
        except pygame.error:
            self.audio_ready = False

        self.create_ui()
        self.minsize(960, 600)
        self.load_music_library()
        self._start_session_tick()
        if HAS_TRAY:
            self._start_tray()

    # ═════════════════════════════════════════════════════════════════════════
    # PERSISTENCE
    # ═════════════════════════════════════════════════════════════════════════

    def _load_json(self, path, default):
        if not os.path.exists(path):
            return default
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return default

    def _save_json(self, path, data):
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
        except OSError:
            pass

    def _load_lines(self, path):
        if not os.path.exists(path):
            return []
        try:
            with open(path, "r", encoding="utf-8") as f:
                return [l.strip() for l in f if l.strip()]
        except OSError:
            return []

    def _save_lines(self, path, lines):
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines))
        except OSError:
            pass

    def _load_todo(self):
        if not os.path.exists(self.todo_path):
            return "- [ ] First task\n- [ ] Second task\n"
        try:
            with open(self.todo_path, "r", encoding="utf-8") as f:
                return f.read()
        except OSError:
            return ""

    def _schedule_todo_save(self, _e=None):
        if self._todo_save_id:
            self.after_cancel(self._todo_save_id)
        self._todo_save_id = self.after(400, self._save_todo_raw)

    def _save_todo_raw(self):
        """Save the raw text backing the checkbox UI."""
        try:
            with open(self.todo_path, "w", encoding="utf-8") as f:
                f.write(self._todo_raw_text())
        except OSError:
            pass
        self._todo_save_id = None

    def _increment_playcount(self, path):
        self.play_counts[path] = self.play_counts.get(path, 0) + 1
        self._save_json(self.plays_path, self.play_counts)
        self._update_top5()

    # ═════════════════════════════════════════════════════════════════════════
    # SESSION TIMER
    # ═════════════════════════════════════════════════════════════════════════

    def _start_session_tick(self):
        self._session_id = self.after(1000, self._session_tick)

    def _session_tick(self):
        elapsed = int(time.monotonic() - self._open_start)
        total   = self.session_seconds + elapsed
        if hasattr(self, "session_label"):
            self.session_label.configure(text=fmt_hms(total))
        self._session_id = self.after(1000, self._session_tick)

    def _save_session(self):
        elapsed = int(time.monotonic() - self._open_start)
        self._save_json(self.sess_path, {"seconds": self.session_seconds + elapsed})

    def reset_session(self):
        self.session_seconds = 0
        self._open_start     = time.monotonic()
        self._save_json(self.sess_path, {"seconds": 0})

    # ═════════════════════════════════════════════════════════════════════════
    # WINDOW
    # ═════════════════════════════════════════════════════════════════════════

    def toggle_fullscreen(self):
        self.attributes("-fullscreen", not self.attributes("-fullscreen"))

    def minimize_app(self):
        self.attributes("-fullscreen", False)
        self.iconify()

    def close_app(self):
        self._save_todo_raw()
        self._save_session()
        for jid in (self._timer_id, self._track_id, self._seek_id,
                    self._todo_save_id, self._session_id, self._anim_id):
            if jid:
                self.after_cancel(jid)
        if self.popout and self.popout.winfo_exists():
            self.popout.destroy()
        if self.audio_ready:
            pygame.mixer.music.stop()
        if self._tray_icon:
            try:
                self._tray_icon.stop()
            except Exception:
                pass
        self.destroy()

    def _hide_to_tray(self):
        self._tray_visible = False
        self.withdraw()

    def _show_from_tray(self):
        self._tray_visible = True
        self.deiconify()
        self.lift()

    # ═════════════════════════════════════════════════════════════════════════
    # SYSTEM TRAY
    # ═════════════════════════════════════════════════════════════════════════

    def _start_tray(self):
        # build a simple 64×64 icon
        img = Image.new("RGB", (64, 64), C_BG)
        d   = ImageDraw.Draw(img)
        d.ellipse((4, 4, 60, 60), fill=C_ACCENT)
        d.polygon([(22, 16), (22, 48), (50, 32)], fill="#ffffff")

        menu = pystray.Menu(
            TrayItem("Show / Hide",  lambda icon, item: self.after(0, self._toggle_tray_visibility)),
            TrayItem("Play / Pause", lambda icon, item: self.after(0, self.toggle_playback)),
            TrayItem("Next Song",    lambda icon, item: self.after(0, self.next_song)),
            pystray.Menu.SEPARATOR,
            TrayItem("Quit",         lambda icon, item: self.after(0, self.close_app)),
        )
        self._tray_icon = pystray.Icon("StudyMusic", img, "Study Music", menu)
        t = threading.Thread(target=self._tray_icon.run, daemon=True)
        t.start()

    def _toggle_tray_visibility(self):
        if self._tray_visible:
            self._hide_to_tray()
        else:
            self._show_from_tray()

    # ═════════════════════════════════════════════════════════════════════════
    # TIMER (POMODORO)
    # ═════════════════════════════════════════════════════════════════════════

    def set_timer(self, minutes):
        if self._timer_id:
            self.after_cancel(self._timer_id)
            self._timer_id = None
        self.timer_running = False
        self.time_left = max(1, int(minutes)) * 60
        self._tick_label()
        self.timer_btn.configure(text="Start")

    def set_timer_custom(self):
        try:
            val = int(self.custom_min_entry.get())
        except ValueError:
            return
        self.set_timer(val)

    def toggle_timer(self):
        if self.timer_running:
            self.timer_running = False
            self.timer_btn.configure(text="Resume")
            if self._timer_id:
                self.after_cancel(self._timer_id)
                self._timer_id = None
        else:
            self.timer_running = True
            self.timer_btn.configure(text="Pause")
            self._tick_timer()

    def _tick_timer(self):
        self._tick_label()
        if not self.timer_running:
            return
        if self.time_left <= 0:
            self.timer_running = False
            self.timer_btn.configure(text="Start")
            return
        self.time_left -= 1
        self._timer_id = self.after(1000, self._tick_timer)

    def _tick_label(self):
        m, s = divmod(self.time_left, 60)
        self.timer_label.configure(text=f"{m:02d}:{s:02d}")

    # ═════════════════════════════════════════════════════════════════════════
    # SEEK
    # ═════════════════════════════════════════════════════════════════════════

    def _true_pos(self):
        if not self.audio_ready:
            return 0.0
        raw = pygame.mixer.music.get_pos()
        return 0.0 if raw < 0 else self._seek_offset + raw / 1000.0

    def _start_seek(self):
        self._stop_seek()
        self._seek_tick()

    def _stop_seek(self):
        if self._seek_id:
            self.after_cancel(self._seek_id)
            self._seek_id = None

    def _seek_tick(self):
        if not self.audio_ready or not self.current_song or not self.is_playing:
            return
        if not self._seek_dragging and self._song_length > 0:
            pos  = min(self._true_pos(), self._song_length)
            frac = pos / self._song_length
            self.seek_slider.set(frac)
            self.seek_elapsed.configure(text=fmt_time(pos))
            self.seek_total.configure(text=fmt_time(self._song_length))
            if self.popout and self.popout.winfo_exists():
                self.po_seek.set(frac)
                self.po_elapsed.configure(text=fmt_time(pos))
        self._seek_id = self.after(350, self._seek_tick)

    def _on_seek_press(self, _e=None):
        self._seek_dragging = True

    def _on_seek_release(self, _e=None):
        self._seek_dragging = False
        self._do_seek(self.seek_slider.get())

    def _on_po_seek_release(self, _e=None):
        self._seek_dragging = False
        frac = self.po_seek.get()
        self.seek_slider.set(frac)
        self._do_seek(frac)

    def _do_seek(self, frac):
        if not self.audio_ready or not self.current_song or self._song_length <= 0:
            return
        target = frac * self._song_length
        self._seek_offset = target
        try:
            pygame.mixer.music.set_pos(target)
        except Exception:
            try:
                pygame.mixer.music.load(self.current_song)
                pygame.mixer.music.play(start=target)
            except Exception:
                pass
        self.seek_elapsed.configure(text=fmt_time(target))
        if self.popout and self.popout.winfo_exists():
            self.po_elapsed.configure(text=fmt_time(target))

    def _reset_seek(self):
        self._seek_offset = 0.0
        self.seek_slider.set(0)
        self.seek_elapsed.configure(text="0:00")
        self.seek_total.configure(text=fmt_time(self._song_length) if self._song_length else "0:00")

    # ═════════════════════════════════════════════════════════════════════════
    # SHUFFLE / LOOP
    # ═════════════════════════════════════════════════════════════════════════

    def toggle_shuffle(self):
        self.shuffle_on = not self.shuffle_on
        self._shuffle_history.clear()
        if self.shuffle_on:
            self.shuffle_btn.configure(fg_color=C_ACCENT, text_color="#fff", text="⇄")
        else:
            self.shuffle_btn.configure(fg_color=C_RAISED, text_color=C_TEXT, text="⇄")
        if hasattr(self, "shuffle_lbl"):
            self.shuffle_lbl.configure(
                text="Shuffle: ON" if self.shuffle_on else "Shuffle: off",
                text_color=C_ACCENT2 if self.shuffle_on else C_MUTED)

    def cycle_loop(self):
        modes = ["none", "one", "all"]
        self.loop_mode = modes[(modes.index(self.loop_mode) + 1) % 3]
        icons  = {"none": "↩",  "one": "🔂", "all": "🔁"}
        colors = {"none": C_RAISED, "one": C_ACCENT, "all": C_ACCENT}
        lbls   = {"none": "Loop: off", "one": "Loop: 1", "all": "Loop: all"}
        self.loop_btn.configure(
            text=icons[self.loop_mode],
            fg_color=colors[self.loop_mode],
            text_color="#fff" if self.loop_mode != "none" else C_TEXT,
        )
        if hasattr(self, "loop_lbl"):
            self.loop_lbl.configure(
                text=lbls[self.loop_mode],
                text_color=C_ACCENT2 if self.loop_mode != "none" else C_MUTED)

    def _next_shuffle_song(self):
        import random
        if not self.songs:
            return None
        pool = [s for s in self.songs if s != self.current_song] or self.songs
        return random.choice(pool)

    # ═════════════════════════════════════════════════════════════════════════
    # QUEUE
    # ═════════════════════════════════════════════════════════════════════════

    def add_to_queue(self, path):
        self.queue.append(path)
        self._repopulate_queue()

    def remove_from_queue(self, index):
        if 0 <= index < len(self.queue):
            self.queue.pop(index)
            self._repopulate_queue()

    def clear_queue(self):
        self.queue.clear()
        self._repopulate_queue()

    def export_queue_m3u(self):
        """
        Write the current queue to queue_export.m3u next to the script.
        Extended m3u format — loadable by VLC, foobar2000, Windows Media Player.
        """
        path = os.path.join(os.getcwd(), "queue_export.m3u")
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("#EXTM3U\n")
                for p in self.queue:
                    dur = int(self._song_len(p))
                    name = self.song_name(p)
                    f.write(f"#EXTINF:{dur},{name}\n{p}\n")
            self.now_status.configure(text=f"Exported {len(self.queue)} tracks")
        except OSError as e:
            self.now_status.configure(text=f"Export failed: {e}")

    def _play_next_from_queue(self):
        if not self.queue:
            return False
        path = self.queue.pop(0)
        self._repopulate_queue()
        if path not in self.songs:
            folder = os.path.dirname(path)
            self.load_folder(folder if folder in self.albums else self.music_dir)
        if path in self.songs:
            self.play_song(path, from_queue=True)
            return True
        return self._play_next_from_queue()

    def _repopulate_queue(self):
        for w in self.queue_list.winfo_children():
            w.destroy()
        self.queue_btns = {}

        self.queue_count_label.configure(
            text=f"{len(self.queue)} in queue" if self.queue else "Queue empty"
        )

        if not self.queue:
            self._label(self.queue_list, "Add songs with +", size=11).pack(pady=8, padx=10, anchor="w")
            return

        for i, path in enumerate(self.queue):
            row = ctk.CTkFrame(self.queue_list, fg_color="transparent")
            row.pack(fill="x", padx=4, pady=2)
            row.grid_columnconfigure(0, weight=0)
            row.grid_columnconfigure(1, weight=1)

            self._label(row, str(i + 1), size=10, color=C_MUTED).grid(
                row=0, column=0, padx=(4, 6), sticky="w")

            btn = ctk.CTkButton(
                row, text=self.song_name(path), anchor="w",
                height=32, corner_radius=6,
                fg_color=C_DIM, hover_color=C_HOVER,
                text_color=C_TEXT, font=(FONT, 11),
                command=lambda p=path, idx=i: self._play_queue_item(p, idx),
            )
            btn.grid(row=0, column=1, sticky="ew")
            self.queue_btns[i] = btn

            rm = ctk.CTkButton(
                row, text="✕", width=26, height=32, corner_radius=6,
                fg_color="transparent", hover_color=C_REDH,
                text_color=C_MUTED, font=(FONT, 10, "bold"),
                command=lambda idx=i: self.remove_from_queue(idx),
            )
            rm.grid(row=0, column=2, padx=(3, 0))

    def _play_queue_item(self, path, index):
        self.queue.pop(index)
        self._repopulate_queue()
        if path not in self.songs:
            folder = os.path.dirname(path)
            self.load_folder(folder if folder in self.albums else self.music_dir)
        if path in self.songs:
            self.play_song(path, from_queue=True)

    # ═════════════════════════════════════════════════════════════════════════
    # FAVOURITES
    # ═════════════════════════════════════════════════════════════════════════

    def toggle_favourite(self, path):
        if path in self.favourites:
            self.favourites.remove(path)
        else:
            self.favourites.append(path)
        self._save_lines(self.favs_path, self.favourites)
        btn = self.star_btns.get(path)
        if btn and btn.winfo_exists():
            starred = path in self.favourites
            btn.configure(text="★" if starred else "☆",
                          text_color=C_STAR if starred else C_MUTED)
        self._repopulate_favs()
        if self.starred_view:
            self.populate_songs()

    def _repopulate_favs(self):
        for w in self.fav_list.winfo_children():
            w.destroy()
        self.fav_btns = {}
        valid = [p for p in self.favourites if os.path.exists(p)]
        if not valid:
            self._label(self.fav_list, "Star songs to see them here", size=11).pack(
                pady=10, padx=12, anchor="w")
            return
        for path in valid:
            row = ctk.CTkFrame(self.fav_list, fg_color="transparent")
            row.pack(fill="x", padx=6, pady=2)
            row.grid_columnconfigure(0, weight=1)

            btn = ctk.CTkButton(
                row, text=self.song_name(path), anchor="w",
                height=36, corner_radius=7,
                fg_color=C_RAISED, hover_color=C_HOVER,
                text_color=C_TEXT, font=(FONT, 12),
                command=lambda p=path: self._play_fav(p),
            )
            btn.grid(row=0, column=0, sticky="ew")
            self.fav_btns[path] = btn

            self._btn(row, "+", lambda p=path: self.add_to_queue(p),
                      w=28, h=36, size=13, bold=True, fg=C_DIM, hv=C_ACCENT).grid(
                row=0, column=1, padx=(3, 0))

            self._btn(row, "✕", lambda p=path: self.toggle_favourite(p),
                      w=28, h=36, size=10, bold=True, fg="transparent", hv=C_REDH,
                      fc=C_MUTED).grid(row=0, column=2, padx=(3, 0))

        self._highlight_fav()

    def _play_fav(self, path):
        if path not in self.songs:
            folder = os.path.dirname(path)
            self.load_folder(folder if folder in self.albums else self.music_dir)
        if path in self.songs:
            self.play_song(path)

    def _highlight_fav(self):
        for p, btn in self.fav_btns.items():
            if btn.winfo_exists():
                btn.configure(fg_color=C_ACCENT if p == self.current_song else C_RAISED)

    def toggle_starred_view(self):
        """Toggle between showing all songs and only starred songs in the main list."""
        self.starred_view = not self.starred_view
        lbl = "★ STARRED PLAYLIST" if self.starred_view else "STARRED"
        self.starred_header_btn.configure(
            text=lbl,
            text_color=C_STAR if self.starred_view else C_MUTED,
        )
        self.populate_songs()

    def toggle_starred_album_filter(self):
        """Toggle album strip to show only albums that contain starred songs."""
        self.starred_album_filter = not self.starred_album_filter
        self.starred_album_btn.configure(
            text="★ Albums" if self.starred_album_filter else "All Albums",
            fg_color=C_ACCENT if self.starred_album_filter else C_RAISED,
            text_color="#fff" if self.starred_album_filter else C_TEXT,
        )
        self.render_album_covers()

    # ═════════════════════════════════════════════════════════════════════════
    # TOP 5 MOST PLAYED
    # ═════════════════════════════════════════════════════════════════════════

    def _update_top5(self):
        if not hasattr(self, "top5_list"):
            return
        for w in self.top5_list.winfo_children():
            w.destroy()
        top = sorted(self.play_counts.items(), key=lambda x: x[1], reverse=True)[:5]
        if not top:
            self._label(self.top5_list, "Play some songs first", size=11).pack(
                pady=6, padx=10, anchor="w")
            return
        for rank, (path, count) in enumerate(top, 1):
            if not os.path.exists(path):
                continue
            row = ctk.CTkFrame(self.top5_list, fg_color="transparent")
            row.pack(fill="x", padx=6, pady=2)
            row.grid_columnconfigure(1, weight=1)

            self._label(row, f"#{rank}", size=10, color=C_ACCENT, bold=True).grid(
                row=0, column=0, padx=(0, 6))

            btn = ctk.CTkButton(
                row, text=f"{self.song_name(path)}  ×{count}", anchor="w",
                height=30, corner_radius=6,
                fg_color=C_RAISED, hover_color=C_HOVER,
                text_color=C_TEXT, font=(FONT, 11),
                command=lambda p=path: self._play_fav(p),
            )
            btn.grid(row=0, column=1, sticky="ew")

    # ═════════════════════════════════════════════════════════════════════════
    # TO-DO CHECKBOXES
    # ═════════════════════════════════════════════════════════════════════════

    # Raw text is the source of truth — we parse it into checkbox rows.
    # Format:  "- [ ] text"  →  unchecked,   "- [x] text"  →  checked
    # Any other line is rendered as a plain label.

    _CB_RE = re.compile(r"^-\s*\[( |x)\]\s*(.*)", re.IGNORECASE)

    def _todo_raw_text(self):
        """Reconstruct raw text from the live checkbox/label widgets."""
        lines = []
        for item in self._todo_items:
            kind = item["kind"]
            if kind == "check":
                mark = "x" if item["var"].get() else " "
                lines.append(f"- [{mark}] {item['text']}")
            else:
                lines.append(item["text"])
        return "\n".join(lines)

    def _build_todo_ui(self, raw_text: str):
        """Parse raw text and render checkbox + plain rows into todo_scroll."""
        for w in self.todo_scroll.winfo_children():
            w.destroy()
        self._todo_items = []

        for line in raw_text.splitlines():
            m = self._CB_RE.match(line)
            if m:
                checked = m.group(1).lower() == "x"
                text    = m.group(2)
                var     = ctk.BooleanVar(value=checked)
                row = ctk.CTkFrame(self.todo_scroll, fg_color="transparent")
                row.pack(fill="x", padx=6, pady=2)
                cb = ctk.CTkCheckBox(
                    row, text=text, variable=var,
                    font=(FONT, 13), text_color=C_TEXT,
                    fg_color=C_ACCENT, hover_color=C_ACCH,
                    border_color=C_BORDER, checkmark_color="#fff",
                    command=self._schedule_todo_save,
                )
                cb.pack(anchor="w")
                # right-click to delete
                cb.bind("<Button-3>", lambda e, r=row, i=len(self._todo_items): self._delete_todo_item(i))
                self._todo_items.append({"kind": "check", "var": var, "text": text, "widget": row})
            else:
                # plain text line (headers, notes, etc.)
                row = ctk.CTkFrame(self.todo_scroll, fg_color="transparent")
                row.pack(fill="x", padx=6, pady=1)
                lbl = ctk.CTkLabel(row, text=line, anchor="w", font=(FONT, 12),
                                   text_color=C_MUTED)
                lbl.pack(anchor="w")
                self._todo_items.append({"kind": "plain", "text": line, "widget": row})

        # "Add task" entry row at bottom
        add_row = ctk.CTkFrame(self.todo_scroll, fg_color="transparent")
        add_row.pack(fill="x", padx=6, pady=(6, 2))
        add_row.grid_columnconfigure(0, weight=1)
        self._new_task_entry = ctk.CTkEntry(
            add_row, placeholder_text="New task…", height=28,
            fg_color=C_DIM, border_color=C_BORDER, font=(FONT, 12),
        )
        self._new_task_entry.grid(row=0, column=0, sticky="ew")
        self._new_task_entry.bind("<Return>", lambda _e: self._add_todo_item())
        self._btn(add_row, "+", self._add_todo_item, w=28, h=28, size=13, bold=True,
                  fg=C_ACCENT, hv=C_ACCH, fc="#fff").grid(row=0, column=1, padx=(4, 0))

    def _add_todo_item(self):
        text = self._new_task_entry.get().strip()
        if not text:
            return
        self._new_task_entry.delete(0, "end")
        raw = self._todo_raw_text()
        raw = raw.rstrip("\n") + f"\n- [ ] {text}\n"
        self._build_todo_ui(raw)
        self._schedule_todo_save()

    def _delete_todo_item(self, index):
        if 0 <= index < len(self._todo_items):
            self._todo_items[index]["widget"].destroy()
            self._todo_items.pop(index)
            self._schedule_todo_save()

    # ═════════════════════════════════════════════════════════════════════════
    # STATS
    # ═════════════════════════════════════════════════════════════════════════

    def _build_stats_content(self, parent):
        """Populate the stats frame."""
        # Session time
        sf = ctk.CTkFrame(parent, fg_color=C_RAISED, corner_radius=8)
        sf.pack(fill="x", padx=10, pady=(6, 4))
        self._label(sf, "SESSION TIME", size=9, bold=True).pack(anchor="w", padx=10, pady=(8, 2))
        row = ctk.CTkFrame(sf, fg_color="transparent")
        row.pack(fill="x", padx=10, pady=(0, 8))
        row.grid_columnconfigure(0, weight=1)
        elapsed = self.session_seconds + int(time.monotonic() - self._open_start)
        self.session_label = ctk.CTkLabel(row, text=fmt_hms(elapsed),
                                          font=(FONT, 20, "bold"), text_color=C_TEXT)
        self.session_label.grid(row=0, column=0, sticky="w")
        self._btn(row, "Reset", self.reset_session, w=50, h=24, size=10,
                  fg=C_DIM, hv=C_REDH, fc=C_MUTED).grid(row=0, column=1)

        # Total songs played (sum of all play counts)
        total_plays = sum(self.play_counts.values())
        pf = ctk.CTkFrame(parent, fg_color=C_RAISED, corner_radius=8)
        pf.pack(fill="x", padx=10, pady=4)
        self._label(pf, "TOTAL PLAYS", size=9, bold=True).pack(anchor="w", padx=10, pady=(8, 2))
        self.total_plays_label = ctk.CTkLabel(pf, text=str(total_plays),
                                              font=(FONT, 20, "bold"), text_color=C_ACCENT)
        self.total_plays_label.pack(anchor="w", padx=10, pady=(0, 8))

        # Unique tracks
        uf = ctk.CTkFrame(parent, fg_color=C_RAISED, corner_radius=8)
        uf.pack(fill="x", padx=10, pady=4)
        self._label(uf, "UNIQUE TRACKS PLAYED", size=9, bold=True).pack(
            anchor="w", padx=10, pady=(8, 2))
        self._label(uf, str(len(self.play_counts)), size=18, bold=True, color=C_TEXT).pack(
            anchor="w", padx=10, pady=(0, 8))

        # Favourite count
        ff = ctk.CTkFrame(parent, fg_color=C_RAISED, corner_radius=8)
        ff.pack(fill="x", padx=10, pady=4)
        self._label(ff, "STARRED SONGS", size=9, bold=True).pack(anchor="w", padx=10, pady=(8, 2))
        self._label(ff, str(len(self.favourites)), size=18, bold=True, color=C_STAR).pack(
            anchor="w", padx=10, pady=(0, 8))

        # Top 5
        t5f = ctk.CTkFrame(parent, fg_color=C_RAISED, corner_radius=8)
        t5f.pack(fill="x", padx=10, pady=(4, 10))
        self._label(t5f, "TOP 5 MOST PLAYED", size=9, bold=True).pack(
            anchor="w", padx=10, pady=(8, 4))
        top = sorted(self.play_counts.items(), key=lambda x: x[1], reverse=True)[:5]
        if top:
            for rank, (path, count) in enumerate(top, 1):
                r = ctk.CTkFrame(t5f, fg_color="transparent")
                r.pack(fill="x", padx=10, pady=1)
                self._label(r, f"#{rank}", size=10, color=C_ACCENT, bold=True).pack(
                    side="left", padx=(0, 6))
                self._label(r, f"{self.song_name(path)}  ×{count}", size=11,
                             color=C_TEXT).pack(side="left")
        else:
            self._label(t5f, "No plays yet", size=11).pack(padx=10, pady=(0, 8))

    # ═════════════════════════════════════════════════════════════════════════
    # UI HELPERS
    # ═════════════════════════════════════════════════════════════════════════

    def _label(self, parent, text, size=11, bold=False, color=C_MUTED, **kw):
        return ctk.CTkLabel(parent, text=text,
                            font=(FONT, size, "bold" if bold else "normal"),
                            text_color=color, **kw)

    def _btn(self, parent, text, cmd, w=None, h=32, fg=C_RAISED, hv=C_HOVER,
             fc=C_TEXT, size=12, bold=False, **kw):
        b = ctk.CTkButton(parent, text=text, command=cmd, height=h,
                          corner_radius=8, fg_color=fg, hover_color=hv,
                          text_color=fc, font=(FONT, size, "bold" if bold else "normal"),
                          **kw)
        if w:
            b.configure(width=w)
        return b

    # ═════════════════════════════════════════════════════════════════════════
    # UI CONSTRUCTION
    # ═════════════════════════════════════════════════════════════════════════

    def create_ui(self):
        self.grid_columnconfigure(0, weight=0)
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self._build_sidebar()
        self._build_main()

    # ── SIDEBAR ──────────────────────────────────────────────────────────────

    def _build_sidebar(self):
        sb = ctk.CTkFrame(self, fg_color=C_SURFACE, corner_radius=0, width=280)
        sb.grid(row=0, column=0, sticky="nsew")
        sb.grid_propagate(False)
        sb.pack_propagate(False)
        # row weights: pomodoro fixed, todo and favs share remaining, stats fixed
        sb.grid_rowconfigure(2, weight=2)
        sb.grid_rowconfigure(3, weight=2)
        sb.grid_rowconfigure(4, weight=1)
        sb.grid_columnconfigure(0, weight=1)

        # title + tray hint
        title_row = ctk.CTkFrame(sb, fg_color="transparent")
        title_row.grid(row=0, column=0, sticky="ew", padx=18, pady=(18, 12))
        title_row.grid_columnconfigure(0, weight=1)
        self._label(title_row, "Study Hub", size=18, bold=True, color=C_TEXT).grid(
            row=0, column=0, sticky="w")
        if HAS_TRAY:
            self._label(title_row, "⎙ tray", size=9, color=C_MUTED).grid(
                row=0, column=1, sticky="e")

        # ── pomodoro ──────────────────────────────────────────────────────────
        pom = ctk.CTkFrame(sb, fg_color=C_BG, corner_radius=10)
        pom.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 6))

        self._label(pom, "POMODORO").pack(anchor="w", padx=14, pady=(12, 0))
        self.timer_label = ctk.CTkLabel(pom, text="25:00",
                                        font=(FONT, 40, "bold"), text_color=C_TEXT)
        self.timer_label.pack(pady=(2, 4))

        # preset buttons
        pf = ctk.CTkFrame(pom, fg_color="transparent")
        pf.pack(fill="x", padx=12, pady=(0, 4))
        pf.grid_columnconfigure((0, 1, 2), weight=1)
        for col, (lbl, m) in enumerate((("25", 25), ("5", 5), ("15", 15))):
            self._btn(pf, lbl, lambda v=m: self.set_timer(v), h=26, size=11, bold=True).grid(
                row=0, column=col, sticky="ew", padx=2)

        # custom interval row
        cf = ctk.CTkFrame(pom, fg_color="transparent")
        cf.pack(fill="x", padx=12, pady=(0, 4))
        cf.grid_columnconfigure(0, weight=1)
        self.custom_min_entry = ctk.CTkEntry(
            cf, placeholder_text="Custom min…", height=26, font=(FONT, 11),
            fg_color=C_RAISED, border_color=C_BORDER)
        self.custom_min_entry.grid(row=0, column=0, sticky="ew", padx=(0, 4))
        self.custom_min_entry.bind("<Return>", lambda _e: self.set_timer_custom())
        self._btn(cf, "Set", self.set_timer_custom, w=40, h=26, size=11).grid(row=0, column=1)

        # start / reset
        bf = ctk.CTkFrame(pom, fg_color="transparent")
        bf.pack(fill="x", padx=12, pady=(0, 12))
        bf.grid_columnconfigure((0, 1), weight=1)
        self.timer_btn = self._btn(bf, "Start", self.toggle_timer, h=30, bold=True,
                                   fg=C_ACCENT, hv=C_ACCH, fc="#fff")
        self.timer_btn.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        self._btn(bf, "Reset", lambda: self.set_timer(25), h=30).grid(
            row=0, column=1, sticky="ew", padx=(3, 0))

        # ── to-do ─────────────────────────────────────────────────────────────
        td = ctk.CTkFrame(sb, fg_color=C_BG, corner_radius=10)
        td.grid(row=2, column=0, sticky="nsew", padx=12, pady=(0, 6))
        td.grid_rowconfigure(1, weight=1)
        td.grid_columnconfigure(0, weight=1)

        self._label(td, "TO DO  (right-click item to delete)").grid(
            row=0, column=0, sticky="w", padx=14, pady=(10, 4))
        self.todo_scroll = ctk.CTkScrollableFrame(td, fg_color="transparent", corner_radius=0)
        self.todo_scroll.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 8))
        self._todo_items = []
        self._build_todo_ui(self._load_todo())

        # ── starred ───────────────────────────────────────────────────────────
        fv = ctk.CTkFrame(sb, fg_color=C_BG, corner_radius=10)
        fv.grid(row=3, column=0, sticky="nsew", padx=12, pady=(0, 6))
        fv.grid_rowconfigure(1, weight=1)
        fv.grid_columnconfigure(0, weight=1)

        # header row with toggle button
        sh = ctk.CTkFrame(fv, fg_color="transparent")
        sh.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 4))
        sh.grid_columnconfigure(0, weight=1)
        self.starred_header_btn = self._btn(
            sh, "STARRED", self.toggle_starred_view,
            h=22, size=10, bold=True, fg="transparent", hv=C_DIM, fc=C_MUTED)
        self.starred_header_btn.grid(row=0, column=0, sticky="w")
        self._label(sh, "click to playlist ›", size=9).grid(row=0, column=1, sticky="e")

        self.fav_list = ctk.CTkScrollableFrame(fv, fg_color="transparent", corner_radius=0)
        self.fav_list.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 8))

        # ── stats ─────────────────────────────────────────────────────────────
        st = ctk.CTkFrame(sb, fg_color=C_BG, corner_radius=10)
        st.grid(row=4, column=0, sticky="nsew", padx=12, pady=(0, 12))
        st.grid_rowconfigure(1, weight=1)
        st.grid_columnconfigure(0, weight=1)

        # collapsible header
        st_hdr = ctk.CTkFrame(st, fg_color="transparent")
        st_hdr.grid(row=0, column=0, sticky="ew", padx=10, pady=(8, 0))
        st_hdr.grid_columnconfigure(0, weight=1)
        self._stats_open = True
        self._stats_btn = self._btn(st_hdr, "STATS ▾", self._toggle_stats,
                                     h=20, size=9, bold=True,
                                     fg="transparent", hv=C_DIM, fc=C_MUTED)
        self._stats_btn.grid(row=0, column=0, sticky="w")

        self.stats_scroll = ctk.CTkScrollableFrame(st, fg_color="transparent", corner_radius=0)
        self.stats_scroll.grid(row=1, column=0, sticky="nsew", padx=0, pady=(2, 6))
        self._build_stats_content(self.stats_scroll)

    def _toggle_stats(self):
        self._stats_open = not self._stats_open
        if self._stats_open:
            self.stats_scroll.grid()
            self._stats_btn.configure(text="STATS ▾")
        else:
            self.stats_scroll.grid_remove()
            self._stats_btn.configure(text="STATS ▸")

    # ── MAIN ─────────────────────────────────────────────────────────────────

    def _build_main(self):
        wrap = ctk.CTkFrame(self, fg_color="transparent")
        wrap.grid(row=0, column=1, sticky="nsew", padx=14, pady=12)
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_columnconfigure(1, weight=0)   # queue column, fixed width
        wrap.grid_rowconfigure(1, weight=1)

        # top bar
        top = ctk.CTkFrame(wrap, fg_color="transparent")
        top.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 8))
        top.grid_columnconfigure(0, weight=1)

        tg = ctk.CTkFrame(top, fg_color="transparent")
        tg.grid(row=0, column=0, sticky="w")
        self._label(tg, "Study Music", size=22, bold=True, color=C_TEXT).pack(anchor="w")
        self.folder_label = self._label(tg, "Music library")
        self.folder_label.pack(anchor="w", pady=(1, 0))

        wb = ctk.CTkFrame(top, fg_color="transparent")
        wb.grid(row=0, column=1, sticky="e")
        for i, (t, cmd, is_close) in enumerate([
            ("—", self.minimize_app,      False),
            ("⛶", self.toggle_fullscreen, False),
            ("✕", self.close_app,         True),
        ]):
            self._btn(wb, t, cmd, w=32, h=28, bold=True, size=12,
                      fg=C_RED if is_close else C_RAISED,
                      hv=C_REDH if is_close else C_HOVER).grid(row=0, column=i, padx=2)

        # content card  (albums + player header | song list | queue column)
        card = ctk.CTkFrame(wrap, fg_color=C_SURFACE, corner_radius=12)
        card.grid(row=1, column=0, columnspan=2, sticky="nsew")
        card.grid_columnconfigure(0, weight=1)   # song list
        card.grid_columnconfigure(1, weight=0)   # queue panel
        card.grid_rowconfigure(2, weight=1)

        # ── album + player header row ─────────────────────────────────────────
        self._build_album_player_header(card)

        # ── search bar ───────────────────────────────────────────────────────
        sr = ctk.CTkFrame(card, fg_color="transparent")
        sr.grid(row=1, column=0, sticky="ew", padx=14, pady=(4, 6))
        sr.grid_columnconfigure(0, weight=1)

        self.search_entry = ctk.CTkEntry(sr, height=32, corner_radius=8, border_width=1,
                                          placeholder_text="Search songs…", font=(FONT, 12),
                                          fg_color=C_RAISED, border_color=C_BORDER)
        self.search_entry.grid(row=0, column=0, sticky="ew")
        self.search_entry.bind("<KeyRelease>", lambda _e: self.populate_songs())

        self.count_label = self._label(sr, "0 songs", size=11)
        self.count_label.grid(row=0, column=1, padx=(8, 0))

        # ── song list ────────────────────────────────────────────────────────
        self.song_list = ctk.CTkScrollableFrame(card, fg_color=C_BG, corner_radius=8)
        self.song_list.grid(row=2, column=0, sticky="nsew", padx=(14, 6), pady=(0, 14))

        # ── queue panel (right, full height from row1) ────────────────────────
        self._build_queue_panel(card)

    def _build_album_player_header(self, card):
        """
        Top row: slim album strip (3 visible) on left,
        now-playing panel (cover + info + controls) fixed on right.
        Layout:
          hdr col 0 (weight=1): albums
          hdr col 1 (weight=0, fixed 340px): now-playing
        """
        hdr = ctk.CTkFrame(card, fg_color="transparent")
        hdr.grid(row=0, column=0, columnspan=2, sticky="ew", padx=12, pady=(12, 4))
        hdr.grid_columnconfigure(0, weight=1)
        hdr.grid_columnconfigure(1, weight=0)

        # ── LEFT: albums ──────────────────────────────────────────────────────
        left = ctk.CTkFrame(hdr, fg_color="transparent")
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        left.grid_columnconfigure(1, weight=1)

        al_hdr = ctk.CTkFrame(left, fg_color="transparent")
        al_hdr.grid(row=0, column=0, columnspan=3, sticky="ew", pady=(0, 4))
        al_hdr.grid_columnconfigure(0, weight=1)
        self._label(al_hdr, "ALBUMS", bold=True, size=10).grid(row=0, column=0, sticky="w")
        self.starred_album_btn = self._btn(
            al_hdr, "All Albums", self.toggle_starred_album_filter,
            w=76, h=20, size=9, fg=C_RAISED, hv=C_HOVER)
        self.starred_album_btn.grid(row=0, column=1, sticky="e")

        # 3 visible albums — smaller cards so they don't eat all the width
        self.visible_albums = 3
        self.prev_album_btn = self._btn(left, "‹", lambda: self.slide_albums(-1),
                                        w=24, h=100, size=16, bold=True, fg=C_BG, hv=C_RAISED)
        self.prev_album_btn.grid(row=1, column=0, sticky="ns", padx=(0, 3))

        self.album_strip = ctk.CTkFrame(left, fg_color="transparent")
        self.album_strip.grid(row=1, column=1, sticky="nsew")

        self.next_album_btn = self._btn(left, "›", lambda: self.slide_albums(1),
                                        w=24, h=100, size=16, bold=True, fg=C_BG, hv=C_RAISED)
        self.next_album_btn.grid(row=1, column=2, sticky="ns", padx=(3, 0))

        # ── RIGHT: now-playing panel (fixed 340 px wide) ──────────────────────
        NP_W = 340
        np = ctk.CTkFrame(hdr, fg_color=C_BG, corner_radius=10, width=NP_W)
        np.grid(row=0, column=1, sticky="nsew")
        np.grid_propagate(False)
        # col 0 = cover (fixed), col 1 = info (expanding)
        np.grid_columnconfigure(0, weight=0, minsize=100)
        np.grid_columnconfigure(1, weight=1)

        # ── Cover art ─────────────────────────────────────────────────────────
        COVER_SZ = 92
        cf = ctk.CTkFrame(np, fg_color="transparent", width=COVER_SZ, height=COVER_SZ)
        cf.grid(row=0, column=0, rowspan=4, padx=(10, 6), pady=(10, 6), sticky="nw")
        cf.grid_propagate(False)
        self.now_cover = ctk.CTkLabel(cf, text="")
        self.now_cover.place(relx=0.5, rely=0.5, anchor="center")

        # ── Title / album ─────────────────────────────────────────────────────
        self.now_title = ctk.CTkLabel(
            np, text="Pick a song",
            font=(FONT, 12, "bold"), text_color=C_TEXT,
            wraplength=200, anchor="w", justify="left")
        self.now_title.grid(row=0, column=1, sticky="ew", padx=(0, 10), pady=(10, 0))

        self.now_album = self._label(np, "Select an album", size=10, anchor="w")
        self.now_album.grid(row=1, column=1, sticky="ew", padx=(0, 10), pady=(0, 4))

        # ── Seek bar ─────────────────────────────────────────────────────────
        sk = ctk.CTkFrame(np, fg_color="transparent")
        sk.grid(row=2, column=1, sticky="ew", padx=(0, 10), pady=(2, 0))
        sk.grid_columnconfigure(0, weight=1)
        self.seek_slider = ctk.CTkSlider(
            sk, from_=0, to=1, height=8, corner_radius=3,
            button_length=6, button_corner_radius=3,
            progress_color=C_ACCENT, button_color=C_ACCENT2,
            button_hover_color="#9fc0ff")
        self.seek_slider.set(0)
        self.seek_slider.grid(row=0, column=0, sticky="ew")
        self.seek_slider.bind("<ButtonPress-1>",   self._on_seek_press)
        self.seek_slider.bind("<ButtonRelease-1>", self._on_seek_release)

        tr = ctk.CTkFrame(sk, fg_color="transparent")
        tr.grid(row=1, column=0, sticky="ew")
        tr.grid_columnconfigure(1, weight=1)
        self.seek_elapsed = self._label(tr, "0:00", size=9)
        self.seek_elapsed.grid(row=0, column=0, sticky="w")
        self.now_status = self._label(tr, "Ready", size=9)
        self.now_status.grid(row=0, column=1)
        self.seek_total = self._label(tr, "0:00", size=9)
        self.seek_total.grid(row=0, column=2, sticky="e")

        # ── Transport controls ────────────────────────────────────────────────
        ctrl = ctk.CTkFrame(np, fg_color="transparent")
        ctrl.grid(row=3, column=1, sticky="ew", padx=(0, 8), pady=(4, 2))
        ctrl.grid_columnconfigure((0, 1, 2), weight=1)
        ctrl.grid_columnconfigure((3, 4), weight=0)

        self.prev_btn = self._btn(ctrl, "⏮", self.previous_song, h=30, size=14, bold=True)
        self.prev_btn.grid(row=0, column=0, sticky="ew", padx=1)
        self.play_btn = self._btn(ctrl, "▶", self.toggle_playback, h=30, size=14, bold=True,
                                  fg=C_ACCENT, hv=C_ACCH, fc="#fff")
        self.play_btn.grid(row=0, column=1, sticky="ew", padx=1)
        self.next_btn = self._btn(ctrl, "⏭", self.next_song, h=30, size=14, bold=True)
        self.next_btn.grid(row=0, column=2, sticky="ew", padx=1)

        # Shuffle — icon + label so it's clear
        self.shuffle_btn = ctk.CTkButton(
            ctrl, text="⇄", width=36, height=30, corner_radius=8,
            fg_color=C_RAISED, hover_color=C_HOVER,
            text_color=C_TEXT, font=(FONT, 14, "bold"),
            command=self.toggle_shuffle)
        self.shuffle_btn.grid(row=0, column=3, padx=(3, 1))

        # Loop — cycles Off→1→All
        self.loop_btn = ctk.CTkButton(
            ctrl, text="↩", width=36, height=30, corner_radius=8,
            fg_color=C_RAISED, hover_color=C_HOVER,
            text_color=C_TEXT, font=(FONT, 13, "bold"),
            command=self.cycle_loop)
        self.loop_btn.grid(row=0, column=4, padx=(1, 0))

        # Shuffle/Loop labels row
        sl_lbl = ctk.CTkFrame(np, fg_color="transparent")
        sl_lbl.grid(row=4, column=1, sticky="ew", padx=(0, 8), pady=(0, 2))
        sl_lbl.grid_columnconfigure(0, weight=1)
        self.shuffle_lbl = self._label(sl_lbl, "Shuffle: off", size=9, color=C_MUTED)
        self.shuffle_lbl.grid(row=0, column=0, sticky="e", padx=(0, 4))
        self.loop_lbl = self._label(sl_lbl, "Loop: off", size=9, color=C_MUTED)
        self.loop_lbl.grid(row=0, column=1, sticky="e")

        # ── Volume + extra buttons ────────────────────────────────────────────
        vr = ctk.CTkFrame(np, fg_color="transparent")
        vr.grid(row=5, column=0, columnspan=2, sticky="ew", padx=10, pady=(0, 8))
        vr.grid_columnconfigure(1, weight=1)
        self._label(vr, "Vol", size=9, bold=True).grid(row=0, column=0, padx=(0, 4))
        self.vol_slider = ctk.CTkSlider(
            vr, from_=0, to=1, height=8,
            command=lambda v: pygame.mixer.music.set_volume(float(v)))
        self.vol_slider.set(0.5)
        self.vol_slider.grid(row=0, column=1, sticky="ew")
        self._btn(vr, "Cover›", self.next_cover_image, w=48, h=22, size=9).grid(
            row=0, column=2, padx=(6, 3))
        self._btn(vr, "Popout", self.open_popout, w=46, h=22, size=9).grid(
            row=0, column=3)

        if not self.audio_ready:
            for w in (self.prev_btn, self.play_btn, self.next_btn,
                      self.shuffle_btn, self.loop_btn,
                      self.vol_slider, self.seek_slider):
                w.configure(state="disabled")
            self.now_status.configure(text="Audio unavailable")

    # ── QUEUE PANEL ──────────────────────────────────────────────────────────

    def _build_queue_panel(self, card):
        qp = ctk.CTkFrame(card, fg_color=C_BG, corner_radius=10, width=260)
        qp.grid(row=1, column=1, rowspan=2, sticky="nsew", padx=(4, 14), pady=(4, 14))
        qp.grid_propagate(False)
        qp.grid_columnconfigure(0, weight=1)
        qp.grid_rowconfigure(2, weight=1)

        hdr = ctk.CTkFrame(qp, fg_color="transparent")
        hdr.grid(row=0, column=0, sticky="ew", padx=12, pady=(10, 4))
        hdr.grid_columnconfigure(0, weight=1)
        self._label(hdr, "UP NEXT", bold=True, size=10).grid(row=0, column=0, sticky="w")
        self.queue_count_label = self._label(hdr, "Queue empty", size=10)
        self.queue_count_label.grid(row=0, column=1, padx=(0, 4))
        self._btn(hdr, "Clear", self.clear_queue, w=42, h=20, size=9,
                  fg=C_DIM, hv=C_REDH, fc=C_MUTED).grid(row=0, column=2)

        # export m3u button
        export_row = ctk.CTkFrame(qp, fg_color="transparent")
        export_row.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 4))
        self._btn(export_row, "Export .m3u", self.export_queue_m3u,
                  h=22, size=9, fg=C_DIM, hv=C_HOVER, fc=C_MUTED).pack(side="left")
        self._label(export_row, "VLC/foobar2k", size=9).pack(side="left", padx=(6, 0))

        self.queue_list = ctk.CTkScrollableFrame(qp, fg_color="transparent", corner_radius=0)
        self.queue_list.grid(row=2, column=0, sticky="nsew", padx=4, pady=(0, 8))

    # ═════════════════════════════════════════════════════════════════════════
    # MUSIC LIBRARY
    # ═════════════════════════════════════════════════════════════════════════

    def load_music_library(self):
        os.makedirs(self.music_dir, exist_ok=True)
        self.albums = self._find_albums()
        self.selected_folder = self.music_dir
        self.load_folder(self.selected_folder)
        self._repopulate_favs()
        self._repopulate_queue()
        self._update_top5()

    def _find_albums(self):
        folders = [self.music_dir]
        for item in sorted(os.listdir(self.music_dir), key=str.lower):
            p = os.path.join(self.music_dir, item)
            if os.path.isdir(p):
                folders.append(p)
        return folders

    def slide_albums(self, d):
        mx = max(0, len(self._visible_albums_list()) - self.visible_albums)
        self.album_offset = min(max(self.album_offset + d, 0), mx)
        self.render_album_covers()

    def _visible_albums_list(self):
        if not self.starred_album_filter:
            return self.albums
        # only albums that have at least one starred song
        starred_set = set(self.favourites)
        result = []
        for folder in self.albums:
            for root, _, files in os.walk(folder):
                if any(os.path.join(root, f) in starred_set for f in files):
                    result.append(folder)
                    break
        return result if result else self.albums

    def _ensure_album_visible(self, album_list):
        if self.selected_folder not in album_list:
            return
        i = album_list.index(self.selected_folder)
        if i < self.album_offset:
            self.album_offset = i
        elif i >= self.album_offset + self.visible_albums:
            self.album_offset = i - self.visible_albums + 1

    def render_album_covers(self):
        for w in self.album_strip.winfo_children():
            w.destroy()
        album_list = self._visible_albums_list()
        self._ensure_album_visible(album_list)
        vis = album_list[self.album_offset: self.album_offset + self.visible_albums]
        for col in range(self.visible_albums):
            self.album_strip.grid_columnconfigure(col, weight=1, uniform="al")
        self._album_btns = {}
        for col, folder in enumerate(vis):
            sel = folder == self.selected_folder
            btn = ctk.CTkButton(
                self.album_strip,
                text=self.album_name(folder),
                image=self.get_album_cover(folder),
                compound="top",
                width=100, height=112,
                corner_radius=10,
                fg_color=C_ACCENT if sel else C_BG,
                hover_color=C_ACCH if sel else C_RAISED,
                text_color=C_TEXT,
                font=(FONT, 10, "bold"),
                command=lambda p=folder, c=col: self._select_album(p, c),
            )
            btn.grid(row=0, column=col, sticky="ew", padx=3)
            self._album_btns[col] = (btn, folder)
        mx = max(0, len(album_list) - self.visible_albums)
        self.prev_album_btn.configure(state="normal" if self.album_offset > 0 else "disabled")
        self.next_album_btn.configure(state="normal" if self.album_offset < mx else "disabled")

    def _select_album(self, folder, col):
        """Start flash animation then load the folder."""
        if self._anim_id:
            self.after_cancel(self._anim_id)
        self._anim_col   = col
        self._anim_step  = 0
        self._anim_target = folder
        self._do_album_anim()

    def _do_album_anim(self):
        step = self._anim_step
        # flash: alternate bright/normal 3 times (6 steps) then load
        STEPS = 6
        if step >= STEPS:
            self.load_folder(self._anim_target)
            self._anim_id = None
            return
        btn_data = self._album_btns.get(self._anim_col)
        if btn_data:
            btn, _ = btn_data
            btn.configure(fg_color=C_ACCENT2 if step % 2 == 0 else C_BG)
        self._anim_step += 1
        self._anim_id = self.after(55, self._do_album_anim)

    # ── naming ────────────────────────────────────────────────────────────────

    def album_name(self, folder):
        return "All Music" if folder == self.music_dir else os.path.basename(folder)

    def album_key(self, folder):
        # Use the folder's absolute path as key — avoids relpath cross-drive errors on Windows.
        return os.path.abspath(folder).replace("\\", "/")

    def song_name(self, path):
        name = os.path.basename(path).strip()
        while True:
            stem, ext = os.path.splitext(name)
            if ext.lower() not in AUDIO_EXTENSIONS:
                return name
            name = stem.strip()

    def song_album_folder(self, path):
        matches = []
        for a in self.albums:
            try:
                if os.path.commonpath([a, path]) == a:
                    matches.append(a)
            except ValueError:
                pass
        return max(matches, key=len) if matches else self.selected_folder

    # ── cover art ─────────────────────────────────────────────────────────────

    def get_album_cover(self, folder, size=(80, 80)):
        key = (folder, size, self._sel_cover(folder))
        if key not in self.cover_cache:
            pil = self._cover_pil(folder).convert("RGB")
            self.cover_cache[key] = ctk.CTkImage(light_image=pil, dark_image=pil, size=size)
        return self.cover_cache[key]

    def _cover_pil(self, folder):
        p = self._sel_cover(folder)
        try:
            img = Image.open(p).convert("RGBA") if p else self._placeholder(self.album_name(folder)).convert("RGBA")
        except OSError:
            img = self._placeholder(self.album_name(folder)).convert("RGBA")
        return self._square(img)

    def _po_cover(self, folder, size=(310, 270)):
        pil = self._cover_pil(folder).convert("RGB")
        return ctk.CTkImage(light_image=pil, dark_image=pil, size=size)

    def _now_cover_img(self, folder, size=(86, 86)):
        pil = self._cover_pil(folder).convert("RGB")
        return ctk.CTkImage(light_image=pil, dark_image=pil, size=size)

    def next_cover_image(self):
        folder = self.song_album_folder(self.current_song) if self.current_song else self.selected_folder
        imgs = self._cover_paths(folder)
        if len(imgs) <= 1:
            return
        key = self.album_key(folder)
        self.cover_indexes[key] = (self.cover_indexes.get(key, 0) + 1) % len(imgs)
        self._save_json(self.cover_path, self.cover_indexes)
        self.cover_cache.clear()
        self.render_album_covers()
        self.update_now_panel()

    def _sel_cover(self, folder):
        imgs = self._cover_paths(folder)
        if not imgs:
            return None
        key = self.album_key(folder)
        idx = self.cover_indexes.get(key, 0) % len(imgs)
        self.cover_indexes[key] = idx
        return imgs[idx]

    def _cover_paths(self, folder):
        exts = (".png", ".jpg", ".jpeg", ".webp")
        name = self.album_name(folder)
        for d in [os.path.join(os.getcwd(), "AlbumCover", name), folder]:
            if not os.path.isdir(d):
                continue
            imgs = [os.path.join(d, f) for f in sorted(os.listdir(d), key=str.lower)
                    if f.lower().endswith(exts)]
            if imgs:
                return imgs
        return []

    def _placeholder(self, name):
        img  = Image.new("RGB", (300, 300), "#111520")
        draw = ImageDraw.Draw(img)
        draw.ellipse((88, 58, 212, 182), fill=C_ACCENT)
        draw.rectangle((106, 148, 194, 222), fill=C_MUTED)
        initial = name[:1].upper() if name else "♪"
        bb = draw.textbbox((0, 0), initial)
        draw.text(((300 - bb[2]) / 2, 236 - bb[3] / 2), initial, fill=C_TEXT)
        return img

    def _square(self, img):
        w, h = img.size
        s = min(w, h)
        img = img.crop(((w - s) // 2, (h - s) // 2, (w + s) // 2, (h + s) // 2))
        return img.resize((300, 300), getattr(Image, "Resampling", Image).LANCZOS)

    # ── folder/song loading ───────────────────────────────────────────────────

    def load_folder(self, folder):
        self.selected_folder = folder
        self.folder_label.configure(text=f"Showing: {self.album_name(folder)}")
        self.songs = []
        for root, _, files in os.walk(folder):
            for fn in files:
                if fn.lower().endswith(AUDIO_EXTENSIONS):
                    self.songs.append(os.path.join(root, fn))
        self.songs.sort(key=lambda p: os.path.basename(p).lower())
        if hasattr(self, "search_entry"):
            self.search_entry.delete(0, "end")
        if self.starred_view:
            self.starred_view = False
            self.starred_header_btn.configure(text="STARRED", text_color=C_MUTED)
        self.render_album_covers()
        self.populate_songs()
        self.update_now_panel()

    def populate_songs(self):
        for w in self.song_list.winfo_children():
            w.destroy()
        self.song_btns = {}
        self.star_btns = {}

        query = self.search_entry.get().strip().lower() if hasattr(self, "search_entry") else ""

        # source pool: all songs or only starred
        if self.starred_view:
            pool = [p for p in self.favourites if os.path.exists(p)]
        else:
            pool = self.songs

        visible = [s for s in pool if query in self.song_name(s).lower()]
        self.count_label.configure(text=f"{len(visible)} songs"
                                    + (" ★" if self.starred_view else ""))

        if not visible:
            msg = ("No starred songs" if self.starred_view
                   else ("No songs found" if self.songs else "Add audio files to the Music folder"))
            self._label(self.song_list, msg, size=12).pack(pady=32, padx=16)
            return

        for song in visible:
            row = ctk.CTkFrame(self.song_list, fg_color="transparent")
            row.pack(fill="x", padx=4, pady=2)
            row.grid_columnconfigure(1, weight=1)

            starred = song in self.favourites
            star = ctk.CTkButton(
                row, text="★" if starred else "☆",
                width=28, height=34, corner_radius=6,
                fg_color="transparent", hover_color=C_RAISED,
                text_color=C_STAR if starred else C_MUTED, font=(FONT, 13),
                command=lambda p=song: self.toggle_favourite(p),
            )
            star.grid(row=0, column=0, padx=(0, 2))
            self.star_btns[song] = star

            btn = ctk.CTkButton(
                row, text=self.song_name(song), anchor="w",
                height=34, corner_radius=6,
                fg_color=C_SURFACE, hover_color=C_HOVER,
                text_color=C_TEXT, font=(FONT, 12),
                command=lambda p=song: self.play_song(p),
            )
            btn.grid(row=0, column=1, sticky="ew")
            self.song_btns[song] = btn

            self._btn(row, "+", lambda p=song: self.add_to_queue(p),
                      w=26, h=34, size=13, bold=True, fg=C_DIM, hv=C_ACCENT).grid(
                row=0, column=2, padx=(2, 0))

        self._highlight_songs()

    # ── playback ──────────────────────────────────────────────────────────────

    def _song_len(self, path):
        # Fast: mutagen reads only the header, not the entire audio file.
        try:
            from mutagen import File as _MF
            f = _MF(path)
            if f is not None and f.info is not None:
                return float(f.info.length)
        except Exception:
            pass
        # Slow fallback (only if mutagen unavailable)
        try:
            return pygame.mixer.Sound(path).get_length()
        except Exception:
            return 0.0

    def play_song(self, path, from_queue=False):
        if not self.audio_ready:
            self.now_status.configure(text="Audio unavailable")
            return
        if path not in self.songs:
            folder = os.path.dirname(path)
            self.load_folder(folder if folder in self.albums else self.music_dir)
            if path not in self.songs:
                self.now_status.configure(text="Song not found")
                return
        try:
            pygame.mixer.music.load(path)
            pygame.mixer.music.play()
        except pygame.error:
            self.now_status.configure(text=f"Cannot play: {self.song_name(path)}")
            self.is_playing = False
            self.play_btn.configure(text="▶")
            return

        # shuffle history
        if self.current_song:
            self._shuffle_history.append(self.current_song)
            if len(self._shuffle_history) > 50:
                self._shuffle_history.pop(0)

        self.current_song  = path
        self.is_playing    = True
        self._seek_offset  = 0.0
        self._song_length  = self._song_len(path)
        self.play_btn.configure(text="⏸")
        self._reset_seek()
        self.update_now_panel("Playing")
        self._highlight_songs()
        self._highlight_fav()
        self._sched_track()
        self._start_seek()
        self._increment_playcount(path)

    def _highlight_songs(self):
        for p, btn in self.song_btns.items():
            btn.configure(fg_color=C_ACCENT if p == self.current_song else C_SURFACE)

    def toggle_playback(self):
        if not self.audio_ready:
            return
        if not self.current_song:
            if self.songs:
                self.play_song(self.songs[0])
            return
        if self.is_playing:
            pygame.mixer.music.pause()
            self.is_playing = False
            self.play_btn.configure(text="▶")
            self.now_status.configure(text="Paused")
            self._stop_seek()
            self._cancel_track()
        else:
            pygame.mixer.music.unpause()
            self.is_playing = True
            self.play_btn.configure(text="⏸")
            self.now_status.configure(text="Playing")
            self._sched_track()
            self._start_seek()
        self.update_popout()

    def _cancel_track(self):
        if self._track_id:
            self.after_cancel(self._track_id)
            self._track_id = None

    def _sched_track(self):
        self._cancel_track()
        self._track_id = self.after(800, self._watch_track)

    def _watch_track(self):
        self._track_id = None
        if not self.audio_ready or not self.current_song or not self.is_playing:
            return
        if pygame.mixer.music.get_busy():
            self._sched_track()
            return
        # song ended
        if self.loop_mode == "one":
            self.play_song(self.current_song)
            return
        if self.queue:
            self._play_next_from_queue()
            return
        if self.loop_mode == "all" or self.shuffle_on:
            self.next_song()
            return
        if len(self.songs) <= 1:
            self.is_playing = False
            self.play_btn.configure(text="▶")
            self.now_status.configure(text="Done")
            self._stop_seek()
            self.update_popout()
            return
        self.next_song()

    def _cur_idx(self):
        try:
            return self.songs.index(self.current_song)
        except ValueError:
            return None

    def previous_song(self):
        if not self.audio_ready or not self.songs:
            return
        # if shuffle, go back in history
        if self.shuffle_on and self._shuffle_history:
            prev = self._shuffle_history.pop()
            if prev in self.songs:
                # don't push current to history again
                tmp = list(self._shuffle_history)
                self.play_song(prev)
                self._shuffle_history = tmp
                return
        if not self.current_song:
            self.play_song(self.songs[-1])
            return
        idx = self._cur_idx()
        if idx is None:
            self.play_song(self.songs[0])
            return
        if pygame.mixer.music.get_pos() > 5000:
            self.play_song(self.current_song)
            return
        self.play_song(self.songs[(idx - 1) % len(self.songs)])

    def next_song(self):
        if not self.audio_ready or not self.songs:
            return
        if self.queue:
            self._play_next_from_queue()
            return
        if self.shuffle_on:
            self.play_song(self._next_shuffle_song())
            return
        idx = self._cur_idx()
        self.play_song(self.songs[0 if idx is None else (idx + 1) % len(self.songs)])

    # ── now panel update ──────────────────────────────────────────────────────

    def update_now_panel(self, status=None):
        folder = self.song_album_folder(self.current_song) if self.current_song else self.selected_folder
        cover  = self._now_cover_img(folder)
        self.now_cover.configure(image=cover, text="")
        if self.current_song:
            self.now_title.configure(text=self.song_name(self.current_song))
            self.now_album.configure(text=self.album_name(folder))
        else:
            self.now_title.configure(text="Pick a song")
            self.now_album.configure(text=self.album_name(self.selected_folder) if self.selected_folder else "")
        if status:
            self.now_status.configure(text=status)
        self.play_btn.configure(text="⏸" if self.is_playing else "▶")
        self.update_popout()

    # ═════════════════════════════════════════════════════════════════════════
    # POPOUT
    # ═════════════════════════════════════════════════════════════════════════

    def open_popout(self):
        if self.popout and self.popout.winfo_exists():
            self.popout.lift()
            self.update_popout()
            return

        pw = ctk.CTkToplevel(self)
        pw.title("Now Playing")
        pw.geometry("310x430")
        pw.resizable(False, False)
        pw.configure(fg_color=C_BG)
        pw.attributes("-topmost", True)
        pw.protocol("WM_DELETE_WINDOW", self.close_popout)
        self.popout = pw

        self.po_cover_label = ctk.CTkLabel(pw, text="", width=310, height=270)
        self.po_cover_label.pack()

        self.po_song_label = ctk.CTkLabel(
            pw, text="No song selected", fg_color="transparent", anchor="w",
            font=(FONT, 13, "bold"), text_color=C_TEXT, wraplength=282)
        self.po_song_label.pack(fill="x", padx=14, pady=(8, 2))

        sk = ctk.CTkFrame(pw, fg_color="transparent")
        sk.pack(fill="x", padx=14, pady=(0, 2))
        sk.grid_columnconfigure(0, weight=1)

        self.po_seek = ctk.CTkSlider(sk, from_=0, to=1, height=10, corner_radius=4,
                                     button_length=8, button_corner_radius=4,
                                     progress_color=C_ACCENT, button_color=C_ACCENT2,
                                     button_hover_color="#9fc0ff")
        self.po_seek.set(0)
        self.po_seek.grid(row=0, column=0, sticky="ew")
        self.po_seek.bind("<ButtonPress-1>",   self._on_seek_press)
        self.po_seek.bind("<ButtonRelease-1>", self._on_po_seek_release)

        tr = ctk.CTkFrame(sk, fg_color="transparent")
        tr.grid(row=1, column=0, sticky="ew", pady=(2, 0))
        tr.grid_columnconfigure(1, weight=1)
        self.po_elapsed = self._label(tr, "0:00", size=10)
        self.po_elapsed.grid(row=0, column=0, sticky="w")
        self.po_total = self._label(tr, "0:00", size=10)
        self.po_total.grid(row=0, column=2, sticky="e")

        ctrl = ctk.CTkFrame(pw, fg_color=C_SURFACE, corner_radius=0)
        ctrl.pack(fill="x")
        ctrl.grid_columnconfigure((0, 1, 2), weight=1)

        self.po_prev = ctk.CTkButton(ctrl, text="⏮", height=46, corner_radius=0,
                                     fg_color=C_SURFACE, hover_color=C_HOVER,
                                     font=(FONT, 18, "bold"), command=self.previous_song)
        self.po_prev.grid(row=0, column=0, sticky="ew")

        self.po_play = ctk.CTkButton(ctrl, text="▶", height=46, corner_radius=0,
                                     fg_color=C_ACCENT, hover_color=C_ACCH, text_color="#fff",
                                     font=(FONT, 18, "bold"), command=self.toggle_playback)
        self.po_play.grid(row=0, column=1, sticky="ew")

        self.po_next = ctk.CTkButton(ctrl, text="⏭", height=46, corner_radius=0,
                                     fg_color=C_SURFACE, hover_color=C_HOVER,
                                     font=(FONT, 18, "bold"), command=self.next_song)
        self.po_next.grid(row=0, column=2, sticky="ew")

        self.update_popout()

    def close_popout(self):
        if self.popout and self.popout.winfo_exists():
            self.popout.destroy()
        self.popout = None

    def update_popout(self):
        if not self.popout or not self.popout.winfo_exists():
            return
        folder = self.song_album_folder(self.current_song) if self.current_song else self.selected_folder
        self._po_cover_img = self._po_cover(folder)
        self.po_cover_label.configure(image=self._po_cover_img, text="")
        self.po_song_label.configure(
            text=self.song_name(self.current_song) if self.current_song else "No song selected")
        state = "normal" if self.audio_ready else "disabled"
        self.po_play.configure(text="⏸" if self.is_playing else "▶", state=state)
        self.po_prev.configure(state=state)
        self.po_next.configure(state=state)
        self.po_total.configure(text=fmt_time(self._song_length))

    # ── top5 placeholder (populated via _update_top5 after sidebar build) ────
    # The sidebar doesn't have a top5_list; top5 is shown inside the stats panel.
    def _update_top5(self):
        # stats panel rebuilds lazily; just refresh total plays label if it exists
        if hasattr(self, "total_plays_label"):
            self.total_plays_label.configure(text=str(sum(self.play_counts.values())))


if __name__ == "__main__":
    app = StudyApp()
    app.mainloop()