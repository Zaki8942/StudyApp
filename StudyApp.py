"""
Study Music
  todo.txt        — to-do list
  favourites.txt  — starred songs (one absolute path per line)
  cover_choices.json — remembered album cover selections
"""

import os
import ctypes
import json

import customtkinter as ctk
import pygame
from PIL import Image, ImageDraw

# ── constants ────────────────────────────────────────────────────────────────
AUDIO_EXTENSIONS = (".mp3", ".wav", ".ogg", ".flac")
TODO_FILE        = "todo.txt"
FAVOURITES_FILE  = "favourites.txt"
COVER_FILE       = "cover_choices.json"

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


def fmt_time(s: float) -> str:
    s = max(0, int(s))
    return f"{s // 60}:{s % 60:02d}"


class StudyApp(ctk.CTk):
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
        self.music_dir       = os.path.join(cwd, "Music")
        self.todo_path       = os.path.join(cwd, TODO_FILE)
        self.favs_path       = os.path.join(cwd, FAVOURITES_FILE)
        self.cover_path      = os.path.join(cwd, COVER_FILE)

        # library state
        self.selected_folder = self.music_dir
        self.albums          = []
        self.album_offset    = 0
        self.visible_albums  = 4
        self.cover_cache     = {}
        self.cover_indexes   = self._load_json(self.cover_path, {})
        self.songs           = []
        self.favourites      = self._load_lines(self.favs_path)
        self.queue           = []   # list of absolute paths, played in order

        # playback state
        self.current_song    = None
        self.is_playing      = False
        self._song_length    = 0.0
        self._seek_offset    = 0.0
        self._seek_dragging  = False

        # widget dicts
        self.song_btns       = {}   # path → song CTkButton
        self.star_btns       = {}   # path → star CTkButton
        self.queue_btns      = {}   # path → queue CTkButton (keyed by list idx actually)
        self.fav_btns        = {}

        # scheduled callbacks
        self.timer_running   = False
        self.time_left       = 25 * 60
        self._timer_id       = None
        self._todo_save_id   = None
        self._track_id       = None
        self._seek_id        = None

        # popout
        self.popout          = None
        self._po_cover_img   = None

        try:
            pygame.mixer.init()
            pygame.mixer.music.set_volume(0.5)
            self.audio_ready = True
        except pygame.error:
            self.audio_ready = False

        self.create_ui()
        self.minsize(960, 600)
        self.load_music_library()

    # ═══════════════════════════════════════════════════════════════════════════
    # PERSISTENCE
    # ═══════════════════════════════════════════════════════════════════════════

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
            return "- "
        try:
            with open(self.todo_path, "r", encoding="utf-8") as f:
                return f.read()
        except OSError:
            return "- "

    def _schedule_todo_save(self, _e=None):
        if self._todo_save_id:
            self.after_cancel(self._todo_save_id)
        self._todo_save_id = self.after(400, self._save_todo)

    def _save_todo(self):
        try:
            with open(self.todo_path, "w", encoding="utf-8") as f:
                f.write(self.todo_box.get("1.0", "end-1c"))
        except OSError:
            pass
        self._todo_save_id = None

    # ═══════════════════════════════════════════════════════════════════════════
    # WINDOW
    # ═══════════════════════════════════════════════════════════════════════════

    def toggle_fullscreen(self):
        self.attributes("-fullscreen", not self.attributes("-fullscreen"))

    def minimize_app(self):
        self.attributes("-fullscreen", False)
        self.iconify()

    def close_app(self):
        self._save_todo()
        for jid in (self._timer_id, self._track_id, self._seek_id, self._todo_save_id):
            if jid:
                self.after_cancel(jid)
        if self.popout and self.popout.winfo_exists():
            self.popout.destroy()
        if self.audio_ready:
            pygame.mixer.music.stop()
        self.destroy()

    # ═══════════════════════════════════════════════════════════════════════════
    # TIMER
    # ═══════════════════════════════════════════════════════════════════════════

    def set_timer(self, minutes):
        if self._timer_id:
            self.after_cancel(self._timer_id)
            self._timer_id = None
        self.timer_running = False
        self.time_left = minutes * 60
        self._tick_label()
        self.timer_btn.configure(text="Start")

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

    # ═══════════════════════════════════════════════════════════════════════════
    # SEEK
    # ═══════════════════════════════════════════════════════════════════════════

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

    # ═══════════════════════════════════════════════════════════════════════════
    # QUEUE
    # ═══════════════════════════════════════════════════════════════════════════

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

    def _play_next_from_queue(self):
        """Pull the first item off the queue and play it."""
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
        # skip missing files and try next
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

            # index badge
            self._label(row, str(i + 1), size=10, color=C_MUTED).grid(
                row=0, column=0, padx=(4, 6), sticky="w"
            )

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
        """Play a specific item and remove it from the queue."""
        self.queue.pop(index)
        self._repopulate_queue()
        if path not in self.songs:
            folder = os.path.dirname(path)
            self.load_folder(folder if folder in self.albums else self.music_dir)
        if path in self.songs:
            self.play_song(path, from_queue=True)

    # ═══════════════════════════════════════════════════════════════════════════
    # FAVOURITES
    # ═══════════════════════════════════════════════════════════════════════════

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

            # queue button
            self._btn(row, "+", lambda p=path: self.add_to_queue(p),
                      w=28, h=36, size=13, bold=True, fg=C_DIM, hv=C_ACCENT).grid(
                row=0, column=1, padx=(3, 0))

            # remove star
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

    # ═══════════════════════════════════════════════════════════════════════════
    # UI HELPERS
    # ═══════════════════════════════════════════════════════════════════════════

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

    def _section(self, parent, title):
        """Return a framed section card with a title label already packed."""
        f = ctk.CTkFrame(parent, fg_color=C_SURFACE, corner_radius=10)
        self._label(f, title, size=10, bold=True).pack(anchor="w", padx=14, pady=(12, 6))
        return f

    # ═══════════════════════════════════════════════════════════════════════════
    # UI CONSTRUCTION
    # ═══════════════════════════════════════════════════════════════════════════

    def create_ui(self):
        self.grid_columnconfigure(0, weight=0)
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self._build_sidebar()
        self._build_main()

    # ── SIDEBAR ──────────────────────────────────────────────────────────────

    def _build_sidebar(self):
        sb = ctk.CTkFrame(self, fg_color=C_SURFACE, corner_radius=0, width=295)
        sb.grid(row=0, column=0, sticky="nsew")
        sb.grid_propagate(False)
        sb.pack_propagate(False)
        sb.grid_rowconfigure(2, weight=2)   # to-do gets 2x space
        sb.grid_rowconfigure(3, weight=3)   # favourites gets 3x space
        sb.grid_columnconfigure(0, weight=1)

        # title
        self._label(sb, "Study Hub", size=18, bold=True, color=C_TEXT).grid(
            row=0, column=0, sticky="w", padx=18, pady=(18, 12))

        # ── pomodoro ─────────────────────────────────────────────────────────
        pom = ctk.CTkFrame(sb, fg_color=C_BG, corner_radius=10)
        pom.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 8))

        self._label(pom, "POMODORO").pack(anchor="w", padx=14, pady=(12, 0))
        self.timer_label = ctk.CTkLabel(pom, text="25:00",
                                        font=(FONT, 44, "bold"), text_color=C_TEXT)
        self.timer_label.pack(pady=(2, 6))

        pf = ctk.CTkFrame(pom, fg_color="transparent")
        pf.pack(fill="x", padx=12, pady=(0, 6))
        pf.grid_columnconfigure((0, 1, 2), weight=1)
        for col, (lbl, m) in enumerate((("25", 25), ("5", 5), ("15", 15))):
            self._btn(pf, lbl, lambda v=m: self.set_timer(v), h=26, size=11, bold=True).grid(
                row=0, column=col, sticky="ew", padx=2)

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
        td.grid(row=2, column=0, sticky="nsew", padx=12, pady=(0, 8))
        td.grid_rowconfigure(1, weight=1)
        td.grid_columnconfigure(0, weight=1)

        self._label(td, "TO DO").grid(row=0, column=0, sticky="w", padx=14, pady=(12, 6))
        self.todo_box = ctk.CTkTextbox(td, corner_radius=8, border_width=0,
                                       fg_color=C_RAISED, text_color=C_TEXT,
                                       font=(FONT, 13), wrap="word")
        self.todo_box.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.todo_box.insert("1.0", self._load_todo())
        self.todo_box.bind("<KeyRelease>", self._schedule_todo_save)

        # ── starred ───────────────────────────────────────────────────────────
        fv = ctk.CTkFrame(sb, fg_color=C_BG, corner_radius=10)
        fv.grid(row=3, column=0, sticky="nsew", padx=12, pady=(0, 12))
        fv.grid_rowconfigure(1, weight=1)
        fv.grid_columnconfigure(0, weight=1)

        self._label(fv, "STARRED").grid(row=0, column=0, sticky="w", padx=14, pady=(12, 6))
        self.fav_list = ctk.CTkScrollableFrame(fv, fg_color="transparent",
                                               corner_radius=0)
        self.fav_list.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 8))

    # ── MAIN ─────────────────────────────────────────────────────────────────

    def _build_main(self):
        wrap = ctk.CTkFrame(self, fg_color="transparent")
        wrap.grid(row=0, column=1, sticky="nsew", padx=18, pady=14)
        wrap.grid_columnconfigure(0, weight=1)
        wrap.grid_columnconfigure(1, weight=0)
        wrap.grid_rowconfigure(1, weight=1)

        # top bar
        top = ctk.CTkFrame(wrap, fg_color="transparent")
        top.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))
        top.grid_columnconfigure(0, weight=1)

        tg = ctk.CTkFrame(top, fg_color="transparent")
        tg.grid(row=0, column=0, sticky="w")
        self._label(tg, "Study Music", size=24, bold=True, color=C_TEXT).pack(anchor="w")
        self.folder_label = self._label(tg, "Music library")
        self.folder_label.pack(anchor="w", pady=(1, 0))

        wb = ctk.CTkFrame(top, fg_color="transparent")
        wb.grid(row=0, column=1, sticky="e")
        for i, (t, cmd, is_close) in enumerate([
            ("—", self.minimize_app,     False),
            ("⛶", self.toggle_fullscreen, False),
            ("✕", self.close_app,        True),
        ]):
            self._btn(wb, t, cmd, w=32, h=28, bold=True, size=12,
                      fg=C_RED if is_close else C_RAISED,
                      hv=C_REDH if is_close else C_HOVER).grid(row=0, column=i, padx=2)

        # content card
        card = ctk.CTkFrame(wrap, fg_color=C_SURFACE, corner_radius=12)
        card.grid(row=1, column=0, columnspan=2, sticky="nsew")
        card.grid_columnconfigure(0, weight=1)
        card.grid_columnconfigure(1, weight=0)
        card.grid_rowconfigure(2, weight=1)

        # albums
        ap = ctk.CTkFrame(card, fg_color="transparent")
        ap.grid(row=0, column=0, columnspan=2, sticky="ew", padx=16, pady=(16, 4))
        ap.grid_columnconfigure(1, weight=1)

        self._label(ap, "ALBUMS").grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 6))

        self.prev_album_btn = self._btn(ap, "‹", lambda: self.slide_albums(-1),
                                        w=28, h=120, size=18, bold=True, fg=C_BG, hv=C_RAISED)
        self.prev_album_btn.grid(row=1, column=0, sticky="ns", padx=(0, 6))

        self.album_strip = ctk.CTkFrame(ap, fg_color="transparent")
        self.album_strip.grid(row=1, column=1, sticky="ew")

        self.next_album_btn = self._btn(ap, "›", lambda: self.slide_albums(1),
                                        w=28, h=120, size=18, bold=True, fg=C_BG, hv=C_RAISED)
        self.next_album_btn.grid(row=1, column=2, sticky="ns", padx=(6, 0))

        # search
        sr = ctk.CTkFrame(card, fg_color="transparent")
        sr.grid(row=1, column=0, sticky="ew", padx=16, pady=(4, 6))
        sr.grid_columnconfigure(0, weight=1)

        self.search_entry = ctk.CTkEntry(sr, height=34, corner_radius=8, border_width=1,
                                         placeholder_text="Search songs…", font=(FONT, 12),
                                         fg_color=C_RAISED, border_color=C_BORDER)
        self.search_entry.grid(row=0, column=0, sticky="ew")
        self.search_entry.bind("<KeyRelease>", lambda _e: self.populate_songs())

        self.count_label = self._label(sr, "0 songs", size=11)
        self.count_label.grid(row=0, column=1, padx=(10, 0))

        # song list
        self.song_list = ctk.CTkScrollableFrame(card, fg_color=C_BG, corner_radius=8)
        self.song_list.grid(row=2, column=0, sticky="nsew", padx=16, pady=(0, 16))

        # right column: now playing + queue
        right = ctk.CTkFrame(card, fg_color="transparent", width=295)
        right.grid(row=1, column=1, rowspan=2, sticky="nsew", padx=(0, 16), pady=(4, 16))
        right.grid_propagate(False)
        right.grid_columnconfigure(0, weight=1)
        right.grid_rowconfigure(0, weight=0)  # now playing
        right.grid_rowconfigure(1, weight=1)  # queue

        self._build_now_panel(right)
        self._build_queue_panel(right)

    # ── NOW PLAYING ───────────────────────────────────────────────────────────

    def _build_now_panel(self, parent):
        np = ctk.CTkFrame(parent, fg_color=C_BG, corner_radius=10)
        np.grid(row=0, column=0, sticky="ew")
        np.grid_columnconfigure(0, weight=1)

        # header
        hdr = ctk.CTkFrame(np, fg_color="transparent")
        hdr.grid(row=0, column=0, sticky="ew", padx=14, pady=(14, 8))
        hdr.grid_columnconfigure(0, weight=1)
        self._label(hdr, "NOW PLAYING").grid(row=0, column=0, sticky="w")

        br = ctk.CTkFrame(hdr, fg_color="transparent")
        br.grid(row=0, column=1)
        self._btn(br, "Cover ›", self.next_cover_image, w=60, h=22, size=10).pack(side="left", padx=(0, 4))
        self._btn(br, "Popout",  self.open_popout,      w=52, h=22, size=10).pack(side="left")

        # cover
        cf = ctk.CTkFrame(np, fg_color="transparent", width=200, height=200)
        cf.grid(row=1, column=0, pady=(0, 10))
        cf.grid_propagate(False)
        self.now_cover = ctk.CTkLabel(cf, text="")
        self.now_cover.place(relx=0.5, rely=0.5, anchor="center")

        # title / album
        self.now_title = ctk.CTkLabel(np, text="Pick a song",
                                      font=(FONT, 14, "bold"), text_color=C_TEXT, wraplength=240)
        self.now_title.grid(row=2, column=0, sticky="ew", padx=14, pady=(0, 1))

        self.now_album = self._label(np, "Select an album", anchor="center")
        self.now_album.grid(row=3, column=0, sticky="ew", padx=14)

        # seek bar
        sk = ctk.CTkFrame(np, fg_color="transparent")
        sk.grid(row=4, column=0, sticky="ew", padx=14, pady=(12, 2))
        sk.grid_columnconfigure(0, weight=1)

        self.seek_slider = ctk.CTkSlider(sk, from_=0, to=1, height=10, corner_radius=4,
                                         button_length=8, button_corner_radius=4,
                                         progress_color=C_ACCENT, button_color=C_ACCENT2,
                                         button_hover_color="#9fc0ff")
        self.seek_slider.set(0)
        self.seek_slider.grid(row=0, column=0, sticky="ew")
        self.seek_slider.bind("<ButtonPress-1>",   self._on_seek_press)
        self.seek_slider.bind("<ButtonRelease-1>", self._on_seek_release)

        tr = ctk.CTkFrame(sk, fg_color="transparent")
        tr.grid(row=1, column=0, sticky="ew", pady=(2, 0))
        tr.grid_columnconfigure(1, weight=1)
        self.seek_elapsed = self._label(tr, "0:00", size=10)
        self.seek_elapsed.grid(row=0, column=0, sticky="w")
        self.now_status = self._label(tr, "Ready", size=10)
        self.now_status.grid(row=0, column=1)
        self.seek_total = self._label(tr, "0:00", size=10)
        self.seek_total.grid(row=0, column=2, sticky="e")

        # controls
        ctrl = ctk.CTkFrame(np, fg_color="transparent")
        ctrl.grid(row=5, column=0, sticky="ew", padx=14, pady=(8, 8))
        ctrl.grid_columnconfigure((0, 1, 2), weight=1)

        self.prev_btn = self._btn(ctrl, "⏮", self.previous_song, h=36, size=14, bold=True)
        self.prev_btn.grid(row=0, column=0, sticky="ew", padx=(0, 3))
        self.play_btn = self._btn(ctrl, "▶", self.toggle_playback, h=36, size=14, bold=True,
                                  fg=C_ACCENT, hv=C_ACCH, fc="#fff")
        self.play_btn.grid(row=0, column=1, sticky="ew", padx=3)
        self.next_btn = self._btn(ctrl, "⏭", self.next_song, h=36, size=14, bold=True)
        self.next_btn.grid(row=0, column=2, sticky="ew", padx=(3, 0))

        # volume
        vr = ctk.CTkFrame(np, fg_color="transparent")
        vr.grid(row=6, column=0, sticky="ew", padx=14, pady=(0, 14))
        vr.grid_columnconfigure(1, weight=1)
        self._label(vr, "Vol", size=10, bold=True).grid(row=0, column=0, sticky="w", padx=(0, 8))
        self.vol_slider = ctk.CTkSlider(vr, from_=0, to=1,
                                        command=lambda v: pygame.mixer.music.set_volume(float(v)))
        self.vol_slider.set(0.5)
        self.vol_slider.grid(row=0, column=1, sticky="ew")

        if not self.audio_ready:
            for w in (self.prev_btn, self.play_btn, self.next_btn, self.vol_slider, self.seek_slider):
                w.configure(state="disabled")
            self.now_status.configure(text="Audio unavailable")

    # ── QUEUE PANEL ───────────────────────────────────────────────────────────

    def _build_queue_panel(self, parent):
        qp = ctk.CTkFrame(parent, fg_color=C_BG, corner_radius=10)
        qp.grid(row=1, column=0, sticky="nsew", pady=(8, 0))
        qp.grid_columnconfigure(0, weight=1)
        qp.grid_rowconfigure(1, weight=1)

        # header row
        hdr = ctk.CTkFrame(qp, fg_color="transparent")
        hdr.grid(row=0, column=0, sticky="ew", padx=14, pady=(12, 6))
        hdr.grid_columnconfigure(0, weight=1)
        self._label(hdr, "UP NEXT").grid(row=0, column=0, sticky="w")

        self.queue_count_label = self._label(hdr, "Queue empty", size=10)
        self.queue_count_label.grid(row=0, column=1, padx=(0, 6))

        self._btn(hdr, "Clear", self.clear_queue, w=46, h=22, size=10,
                  fg=C_DIM, hv=C_REDH, fc=C_MUTED).grid(row=0, column=2)

        self.queue_list = ctk.CTkScrollableFrame(qp, fg_color="transparent", corner_radius=0)
        self.queue_list.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 8))

    # ═══════════════════════════════════════════════════════════════════════════
    # MUSIC LIBRARY
    # ═══════════════════════════════════════════════════════════════════════════

    def load_music_library(self):
        os.makedirs(self.music_dir, exist_ok=True)
        self.albums = self._find_albums()
        if self.selected_folder not in self.albums:
            self.selected_folder = self.music_dir
        self.load_folder(self.selected_folder)
        self._repopulate_favs()
        self._repopulate_queue()

    def _find_albums(self):
        folders = [self.music_dir]
        for item in sorted(os.listdir(self.music_dir), key=str.lower):
            p = os.path.join(self.music_dir, item)
            if os.path.isdir(p):
                folders.append(p)
        return folders

    def slide_albums(self, d):
        mx = max(0, len(self.albums) - self.visible_albums)
        self.album_offset = min(max(self.album_offset + d, 0), mx)
        self.render_album_covers()

    def _ensure_album_visible(self):
        if self.selected_folder not in self.albums:
            return
        i = self.albums.index(self.selected_folder)
        if i < self.album_offset:
            self.album_offset = i
        elif i >= self.album_offset + self.visible_albums:
            self.album_offset = i - self.visible_albums + 1

    def render_album_covers(self):
        for w in self.album_strip.winfo_children():
            w.destroy()
        self._ensure_album_visible()
        vis = self.albums[self.album_offset: self.album_offset + self.visible_albums]
        for col in range(self.visible_albums):
            self.album_strip.grid_columnconfigure(col, weight=1, uniform="al")
        for col, folder in enumerate(vis):
            sel = folder == self.selected_folder
            ctk.CTkButton(
                self.album_strip,
                text=self.album_name(folder),
                image=self.get_album_cover(folder),
                compound="top",
                width=126, height=140,
                corner_radius=10,
                fg_color=C_ACCENT if sel else C_BG,
                hover_color=C_ACCH if sel else C_RAISED,
                text_color=C_TEXT,
                font=(FONT, 11, "bold"),
                command=lambda p=folder: self.load_folder(p),
            ).grid(row=0, column=col, sticky="ew", padx=4)
        mx = max(0, len(self.albums) - self.visible_albums)
        self.prev_album_btn.configure(state="normal" if self.album_offset > 0 else "disabled")
        self.next_album_btn.configure(state="normal" if self.album_offset < mx else "disabled")

    # ── naming ────────────────────────────────────────────────────────────────

    def album_name(self, folder):
        return "All Music" if folder == self.music_dir else os.path.basename(folder)

    def album_key(self, folder):
        return os.path.relpath(folder, self.music_dir).replace("\\", "/")

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

    def get_album_cover(self, folder, size=(100, 100)):
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
        self.search_entry.delete(0, "end")
        self.render_album_covers()
        self.populate_songs()
        self.update_now_panel()

    def populate_songs(self):
        for w in self.song_list.winfo_children():
            w.destroy()
        self.song_btns  = {}
        self.star_btns  = {}

        query   = self.search_entry.get().strip().lower()
        visible = [s for s in self.songs if query in self.song_name(s).lower()]
        self.count_label.configure(text=f"{len(visible)} songs")

        if not visible:
            msg = "No songs found" if self.songs else "Add audio files to the Music folder"
            self._label(self.song_list, msg, size=12).pack(pady=32, padx=16)
            return

        for song in visible:
            row = ctk.CTkFrame(self.song_list, fg_color="transparent")
            row.pack(fill="x", padx=4, pady=2)
            row.grid_columnconfigure(1, weight=1)

            # star
            starred = song in self.favourites
            star = ctk.CTkButton(
                row, text="★" if starred else "☆",
                width=28, height=36, corner_radius=6,
                fg_color="transparent", hover_color=C_RAISED,
                text_color=C_STAR if starred else C_MUTED,
                font=(FONT, 14),
                command=lambda p=song: self.toggle_favourite(p),
            )
            star.grid(row=0, column=0, padx=(0, 2))
            self.star_btns[song] = star

            # song name
            btn = ctk.CTkButton(
                row, text=self.song_name(song), anchor="w",
                height=36, corner_radius=6,
                fg_color=C_SURFACE, hover_color=C_HOVER,
                text_color=C_TEXT, font=(FONT, 12),
                command=lambda p=song: self.play_song(p),
            )
            btn.grid(row=0, column=1, sticky="ew")
            self.song_btns[song] = btn

            # add to queue
            self._btn(row, "+", lambda p=song: self.add_to_queue(p),
                      w=26, h=36, size=13, bold=True, fg=C_DIM, hv=C_ACCENT).grid(
                row=0, column=2, padx=(2, 0))

        self._highlight_songs()

    # ── playback ──────────────────────────────────────────────────────────────

    def _song_len(self, path):
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

        self.current_song   = path
        self.is_playing     = True
        self._seek_offset   = 0.0
        self._song_length   = self._song_len(path)
        self.play_btn.configure(text="⏸")
        self._reset_seek()
        self.update_now_panel("Playing")
        self._highlight_songs()
        self._highlight_fav()
        self._sched_track()
        self._start_seek()

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
        # song ended — check queue first
        if self.queue:
            self._play_next_from_queue()
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
        idx = self._cur_idx()
        self.play_song(self.songs[0 if idx is None else (idx + 1) % len(self.songs)])

    # ── now panel update ──────────────────────────────────────────────────────

    def update_now_panel(self, status=None):
        folder = self.song_album_folder(self.current_song) if self.current_song else self.selected_folder
        cover  = self.get_album_cover(folder, size=(196, 196))
        self.now_cover.configure(image=cover, text="")
        if self.current_song:
            self.now_title.configure(text=self.song_name(self.current_song))
            self.now_album.configure(text=self.album_name(folder))
        else:
            self.now_title.configure(text="Pick a song")
            self.now_album.configure(text=self.album_name(self.selected_folder))
        if status:
            self.now_status.configure(text=status)
        self.play_btn.configure(text="⏸" if self.is_playing else "▶")
        self.update_popout()

    # ═══════════════════════════════════════════════════════════════════════════
    # POPOUT
    # ═══════════════════════════════════════════════════════════════════════════

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


if __name__ == "__main__":
    app = StudyApp()
    app.mainloop()