import os
import sys
import json
import threading
import time
import requests
import random
import hashlib
import webbrowser
import re
import base64
from io import BytesIO
from PIL import Image
import tkinter as tk
import tkinter.filedialog as filedialog
import tkinter.messagebox as messagebox
import customtkinter as ctk
import yt_dlp
import vlc

# --- SYSTEM SETUP ---
def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(os.path.expanduser("~"), ".bastify")
if not os.path.exists(DATA_DIR): os.makedirs(DATA_DIR)
DATA_FILE = os.path.join(DATA_DIR, "bastify_v50_perf.json")

# --- THEME PRESETS ---
THEME_PRESETS = {
    "Spotify Green": {"primary": "#1DB954", "sidebar": ("#FFFFFF", "#181818"), "bg": ("#F3F4F6", "#121212")},
    "Ocean Blue": {"primary": "#3B8ED0", "sidebar": ("#F0F8FF", "#111b21"), "bg": ("#E6F2FF", "#0f172a")},
    "Cherry Red": {"primary": "#E11D48", "sidebar": ("#FFF0F5", "#1f0f0f"), "bg": ("#FFE4E1", "#120505")},
    "Royal Gold": {"primary": "#D4AF37", "sidebar": ("#FFFAF0", "#1c190f"), "bg": ("#FFF8DC", "#0f0e05")},
    "Cyber Purple": {"primary": "#9333EA", "sidebar": ("#F3E5F5", "#180a1f"), "bg": ("#F3E5F5", "#0d0412")},
    "Toxic Neon": {"primary": "#CCFF00", "sidebar": ("#F9FFF0", "#141a00"), "bg": ("#F0FFD1", "#0a0d00")}
}

COLORS = {
    "bg":       ("#F3F4F6", "#121212"),
    "sidebar":  ("#FFFFFF", "#181818"),
    "card":     ("#FFFFFF", "#222222"),
    "primary":  "#1DB954", 
    "text":     ("#111827", "#FFFFFF"),
    "text_sub": ("#6B7280", "#B3B3B3"),
    "hover":    ("#E5E7EB", "#333333"),
    "danger":   "#EF4444",
    "separator":("#D1D5DB", "#2B2B2B"),
    "panel":    ("#F9FAFB", "#252525"),
    "icon":     ("#374151", "#E5E7EB")
}

# --- VLC SETUP ---
def setup_vlc():
    search_paths = [r'C:\Program Files\VideoLAN\VLC', r'C:\Program Files (x86)\VideoLAN\VLC']
    for path in search_paths:
        if os.path.exists(path):
            os.add_dll_directory(path)
            return True
    return False

setup_vlc()

class Bastify(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("Bastify - PENIS Edition")
        self.geometry("1400x950")
        
        self.data_lock = threading.Lock()

        self.music_dir = os.path.join(os.path.expanduser("~"), "Music", "Bastify-Musik")
        if not os.path.exists(self.music_dir): os.makedirs(self.music_dir)
        self.cache_dir = os.path.join(DATA_DIR, "_cache")
        if not os.path.exists(self.cache_dir): os.makedirs(self.cache_dir)

        self.db = self.load_data()
        self.appearance_mode = self.db.get("_settings", {}).get("mode", "dark")
        ctk.set_appearance_mode(self.appearance_mode)
        
        saved_theme = self.db.get("_settings", {}).get("theme_name", "Spotify Green")
        if saved_theme in THEME_PRESETS:
            self.apply_theme_colors(saved_theme)
        self.current_theme_name = saved_theme

        self.sp_client_id = self.db.get("_settings", {}).get("sp_id", "")
        self.sp_client_secret = self.db.get("_settings", {}).get("sp_secret", "")
        
        self.current_playlist = self.db.get("_session", {}).get("last_playlist", "Favoriten")
        valid_keys = [k for k in self.db.keys() if not k.startswith("_")]
        if self.current_playlist not in self.db:
            if valid_keys: self.current_playlist = valid_keys[0]
            else:
                self.current_playlist = "Favoriten"
                self.db[self.current_playlist] = []

        self.last_volume = self.db.get("_session", {}).get("volume", 70)
        self.shuffle = self.db.get("_session", {}).get("shuffle", False)
        self.repeat = self.db.get("_session", {}).get("repeat", "none")
        self.current_index = self.db.get("_session", {}).get("last_index", -1)
        
        self.page = 0
        self.items_per_page = 50 

        try:
            self.instance = vlc.Instance("--no-xlib --quiet --audio-filter=normvol --norm-max-level=2.0 --network-caching=3000")
            self.player = self.instance.media_player_new()
            self.player.audio_set_volume(int(self.last_volume))
            self.equalizer = vlc.AudioEqualizer()
            self.player.set_equalizer(self.equalizer)
        except:
            messagebox.showerror("Fehler", "VLC Player fehlt! Bitte VLC installieren.")
            sys.exit()
        
        self.eq_active_preset = "Normal"
        self.queue = []
        self.filter_var = ctk.StringVar()
        try: self.filter_var.trace_add("write", self.filter_change_event)
        except: self.filter_var.trace("w", self.filter_change_event)
        
        self.sleep_timer_end = None
        self.current_cover_data = None 
        self.current_image_obj = None
        self.drag_data = {"item_idx": None, "frames": []}
        self.is_slider_dragging = False
        self.settings_visible = False
        
        self.is_muted = False
        self.saved_volume = self.last_volume
        self.show_remaining_time = False 
        
        self.stats_frame = None

        self.sort_popup = None
        self.sleep_popup = None
        self.speed_popup = None
        self.eq_popup = None

        self.bind("<space>", self.on_space_press)
        self.bind("<Right>", self.on_right_press)
        self.bind("<Left>", self.on_left_press)
        self.bind("<Control-f>", lambda e: self.entry.focus_set())
        self.bind_all("<Button-1>", self.on_global_click)

        self.configure(fg_color=COLORS["bg"])
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self.setup_sidebar()
        self.setup_main_area()
        self.setup_player_bar()

        self.update_sidebar_ui()
        self.update_main_song_list()
        
        if self.current_index != -1 and self.db[self.current_playlist]:
            try:
                s = self.db[self.current_playlist][self.current_index]
                self.mini_title.configure(text=s['title'])
                if s.get('thumb'): threading.Thread(target=self.load_thumb, args=(s,), daemon=True).start()
            except: pass

        threading.Thread(target=self.bg_loop, daemon=True).start()

    # --- UI SETUP ---
    def setup_sidebar(self):
        self.sidebar = ctk.CTkFrame(self, width=280, corner_radius=0, fg_color=COLORS["sidebar"])
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.bind("<MouseWheel>", self.on_vol_scroll) 
        
        self.logo_label = ctk.CTkLabel(self.sidebar, text="Bastify", font=("Helvetica", 32, "bold"), text_color=COLORS["primary"])
        self.logo_label.pack(pady=(40, 5))
        ctk.CTkLabel(self.sidebar, text="FINAL UI", font=("Arial", 10, "bold"), text_color=COLORS["text_sub"]).pack(pady=(0, 20))
        
        self.user_btn = ctk.CTkButton(self.sidebar, text="⚙  Einstellungen", height=40, fg_color=COLORS["panel"], text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.toggle_settings_menu)
        self.user_btn.pack(pady=10, padx=20, fill="x")
        
        self.settings_panel = ctk.CTkFrame(self.sidebar, fg_color=COLORS["panel"], corner_radius=10, border_width=1, border_color=COLORS["separator"])
        
        self.sep1 = ctk.CTkFrame(self.sidebar, height=2, fg_color=COLORS["separator"])
        self.sep1.pack(fill="x", padx=20, pady=10)
        
        ctk.CTkLabel(self.sidebar, text="PLAYLISTS", font=("Arial", 11, "bold"), text_color=COLORS["text_sub"]).pack(anchor="w", padx=25, pady=(10, 5))
        self.pl_entry = ctk.CTkEntry(self.sidebar, placeholder_text="Neue Playlist...", height=35, fg_color=COLORS["panel"], text_color=COLORS["text"], border_width=1, border_color=COLORS["separator"])
        self.pl_entry.pack(fill="x", padx=20, pady=5)
        
        self.create_pl_btn = ctk.CTkButton(self.sidebar, text="➕ Erstellen", fg_color=COLORS["primary"], text_color="white", hover_color=COLORS["primary"], command=self.create_playlist)
        self.create_pl_btn.pack(fill="x", padx=20, pady=5)
        
        # STATISTIK BUTTON
        ctk.CTkButton(self.sidebar, text="📊 Statistik", fg_color="transparent", text_color=COLORS["text"], hover_color=COLORS["hover"], border_width=1, border_color=COLORS["separator"], command=self.show_statistics).pack(fill="x", padx=20, pady=5)

        self.sep2 = ctk.CTkFrame(self.sidebar, height=2, fg_color=COLORS["separator"])
        self.sep2.pack(fill="x", padx=20, pady=10)
        ctk.CTkLabel(self.sidebar, text="BIBLIOTHEK", font=("Arial", 11, "bold"), text_color=COLORS["text_sub"]).pack(anchor="w", padx=25, pady=(5, 5))
        self.pl_scroll = ctk.CTkScrollableFrame(self.sidebar, fg_color="transparent")
        self.pl_scroll.pack(fill="both", expand=True, padx=5, pady=5)
        
        self.help_btn = ctk.CTkButton(self.sidebar, text="?", width=30, height=30, fg_color="transparent", border_width=1, border_color=COLORS["text_sub"], text_color=COLORS["text_sub"], command=self.show_shortcuts)
        self.help_btn.place(relx=0.85, rely=0.97, anchor="se")

    def setup_main_area(self):
        self.main = ctk.CTkFrame(self, corner_radius=0, fg_color="transparent")
        self.main.grid(row=0, column=1, sticky="nsew")
        
        self.header = ctk.CTkFrame(self.main, fg_color=COLORS["sidebar"], corner_radius=0, height=80)
        self.header.pack(fill="x", side="top", anchor="n") # Fix: Layout
        
        self.header_inner = ctk.CTkFrame(self.header, fg_color="transparent")
        self.header_inner.pack(fill="x", padx=30, pady=20)
        self.entry = ctk.CTkEntry(self.header_inner, placeholder_text="Link / Suche (Strg+F)", width=300, height=40, border_width=1, border_color=COLORS["separator"], fg_color=COLORS["bg"], text_color=COLORS["text"])
        self.entry.pack(side="left", padx=(0, 10))
        ctk.CTkButton(self.header_inner, text="📋", width=40, height=40, fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.quick_clipboard_import).pack(side="left", padx=5)
        self.add_btn = ctk.CTkButton(self.header_inner, text="📥 Import", fg_color=COLORS["primary"], width=90, height=40, command=self.add_by_search)
        self.add_btn.pack(side="left")
        ctk.CTkButton(self.header_inner, text="📝 Liste", fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], width=80, height=40, command=self.open_text_import).pack(side="left", padx=10)
        ctk.CTkButton(self.header_inner, text="📂 MP3", fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], width=80, height=40, command=self.add_local_files).pack(side="left", padx=5)
        self.sleep_btn = ctk.CTkButton(self.header_inner, text="🌙", width=40, height=40, fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.open_sleep_menu)
        self.sleep_btn.pack(side="right", padx=5)
        self.status_lbl = ctk.CTkLabel(self.header_inner, text="", text_color=COLORS["text_sub"])
        self.status_lbl.pack(side="right", padx=20)
        
        self.tool_row = ctk.CTkFrame(self.main, fg_color="transparent")
        self.tool_row.pack(fill="x", padx=30, pady=(20, 10), side="top", anchor="n") # Fix: Layout
        
        self.filter_entry = ctk.CTkEntry(self.tool_row, textvariable=self.filter_var, placeholder_text="🔍 Filter...", width=180, height=32, fg_color=COLORS["sidebar"], border_width=1, border_color=COLORS["separator"], text_color=COLORS["text"])
        self.filter_entry.pack(side="left", padx=(0, 10))
        ctk.CTkButton(self.tool_row, text="<", width=30, height=32, fg_color=COLORS["bg"], text_color=COLORS["text"], command=self.prev_page).pack(side="left", padx=2)
        self.page_lbl = ctk.CTkLabel(self.tool_row, text="1", width=30, text_color=COLORS["text_sub"])
        self.page_lbl.pack(side="left", padx=2)
        ctk.CTkButton(self.tool_row, text=">", width=30, height=32, fg_color=COLORS["bg"], text_color=COLORS["text"], command=self.next_page).pack(side="left", padx=2)
        shuff_col = COLORS["primary"] if self.shuffle else COLORS["bg"]
        self.shuffle_btn = ctk.CTkButton(self.tool_row, text="🔀 Shuffle", width=80, height=32, fg_color=shuff_col, text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.toggle_shuffle)
        self.shuffle_btn.pack(side="left", padx=(10, 5))
        self.sort_btn = ctk.CTkButton(self.tool_row, text="Sortieren ▾", width=80, height=32, fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.open_sort_menu)
        self.sort_btn.pack(side="left", padx=5)
        rep_col = COLORS["primary"] if self.repeat != "none" else COLORS["bg"]
        self.repeat_btn = ctk.CTkButton(self.tool_row, text=f"🔁 {self.repeat}", width=80, height=32, fg_color=rep_col, text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.toggle_repeat)
        self.repeat_btn.pack(side="left", padx=5)
        self.bass_btn = ctk.CTkButton(self.tool_row, text="EQ ▾", width=70, height=32, fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], border_width=1, border_color=COLORS["text_sub"], command=self.open_eq_menu)
        self.bass_btn.pack(side="left", padx=5)
        self.speed_btn = ctk.CTkButton(self.tool_row, text="1.0x", width=60, height=32, fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], border_width=1, border_color=COLORS["text_sub"], command=self.open_speed_menu)
        self.speed_btn.pack(side="left", padx=5)
        ctk.CTkButton(self.tool_row, text="Ordner ↗", width=70, height=32, fg_color="transparent", border_width=1, border_color="#555", text_color=COLORS["text_sub"], command=self.open_music_folder).pack(side="right")
        
        self.song_frame = ctk.CTkScrollableFrame(self.main, fg_color="transparent")
        self.song_frame.pack(fill="both", expand=True, padx=20, pady=10, side="top", anchor="n") # Fix: Layout

    def setup_player_bar(self):
        self.player_bar = ctk.CTkFrame(self, height=110, corner_radius=0, fg_color=COLORS["sidebar"])
        self.player_bar.grid(row=1, column=0, columnspan=2, sticky="ew")
        self.player_bar.grid_columnconfigure(1, weight=1)
        self.info_box = ctk.CTkFrame(self.player_bar, fg_color="transparent")
        self.info_box.grid(row=0, column=0, padx=20, sticky="w")
        self.mini_img = ctk.CTkLabel(self.info_box, text="🎵", width=60, height=60, fg_color=COLORS["bg"], corner_radius=5)
        self.mini_img.pack(side="left")
        self.mini_img.bind("<Button-1>", self.open_big_view)
        self.title_frm = ctk.CTkFrame(self.info_box, fg_color="transparent")
        self.title_frm.pack(side="left", padx=10)
        self.mini_title = ctk.CTkLabel(self.title_frm, text="Kein Song", font=("Arial", 13, "bold"), text_color=COLORS["text"], anchor="w", width=200)
        self.mini_title.pack(anchor="w")
        self.dl_btn = ctk.CTkButton(self.title_frm, text="⬇ Save", height=18, width=60, fg_color="transparent", text_color=COLORS["text_sub"], command=self.download_current)
        self.dl_btn.pack(anchor="w", side="left")
        self.lyrics_btn = ctk.CTkButton(self.title_frm, text="🎤 Text", height=18, width=60, fg_color="transparent", text_color=COLORS["primary"], hover_color=COLORS["bg"], command=self.open_lyrics)
        self.lyrics_btn.pack(anchor="w", side="left", padx=5)
        
        self.ctrl_box = ctk.CTkFrame(self.player_bar, fg_color="transparent")
        self.ctrl_box.grid(row=0, column=1)
        self.btns = ctk.CTkFrame(self.ctrl_box, fg_color="transparent")
        self.btns.pack(pady=5)
        ctk.CTkButton(self.btns, text="⏮", width=40, fg_color="transparent", text_color=COLORS["text"], font=("Arial", 20), command=self.play_prev).pack(side="left", padx=10)
        self.play_btn = ctk.CTkButton(self.btns, text="▶", width=50, height=50, corner_radius=25, fg_color=COLORS["text"], text_color=COLORS["bg"], font=("Arial", 20), hover_color=COLORS["text_sub"], command=self.toggle_pause)
        self.play_btn.pack(side="left", padx=10)
        ctk.CTkButton(self.btns, text="⏭", width=40, fg_color="transparent", text_color=COLORS["text"], font=("Arial", 20), command=self.play_next).pack(side="left", padx=10)
        self.time_frame = ctk.CTkFrame(self.ctrl_box, fg_color="transparent")
        self.time_frame.pack(fill="x")
        self.time_now = ctk.CTkLabel(self.time_frame, text="00:00", text_color=COLORS["text_sub"], font=("Arial", 11), cursor="hand2")
        self.time_now.pack(side="left", padx=10)
        self.time_now.bind("<Button-1>", self.toggle_time_mode)
        self.progress = ctk.CTkSlider(self.time_frame, from_=0, to=1000, progress_color=COLORS["primary"], width=400, command=self.seek_song)
        self.progress.pack(side="left", fill="x", expand=True)
        self.progress.set(0)
        self.progress.bind("<Button-1>", lambda e: self.set_dragging(True))
        self.progress.bind("<ButtonRelease-1>", lambda e: self.set_dragging(False))
        self.time_total = ctk.CTkLabel(self.time_frame, text="00:00", text_color=COLORS["text_sub"], font=("Arial", 11))
        self.time_total.pack(side="left", padx=10)
        self.vol_box = ctk.CTkFrame(self.player_bar, fg_color="transparent")
        self.vol_box.grid(row=0, column=2, padx=20, sticky="e")
        ctk.CTkButton(self.vol_box, text="🔲", width=30, fg_color="transparent", text_color=COLORS["text"], command=self.toggle_mini_player).pack(side="left")
        self.vol_icon = ctk.CTkLabel(self.vol_box, text="🔊", text_color=COLORS["icon"], font=("Arial", 14))
        self.vol_icon.pack(side="left", padx=(5,0))
        self.vol_icon.bind("<Button-1>", self.toggle_mute)
        self.vol_slider = ctk.CTkSlider(self.vol_box, from_=0, to=100, width=100, command=self.change_volume)
        self.vol_slider.set(self.last_volume) 
        self.vol_slider.pack(side="left", padx=10)
        self.vol_slider.bind("<MouseWheel>", self.on_vol_scroll)

    # --- STATISTIK & TABS ---
    def show_statistics(self):
        if self.stats_frame is not None and self.stats_frame.winfo_exists():
            return

        self.header.pack_forget()
        self.tool_row.pack_forget()
        self.song_frame.pack_forget()
        
        self.stats_frame = ctk.CTkScrollableFrame(self.main, fg_color="transparent")
        self.stats_frame.pack(fill="both", expand=True, padx=20, pady=20)
        
        ctk.CTkLabel(self.stats_frame, text="Dein Statistik-Dashboard", font=("Helvetica", 28, "bold"), text_color=COLORS["primary"]).pack(pady=(10, 30))
        
        all_songs = []
        total_plays = 0
        for pl_name, songs in self.db.items():
            if pl_name.startswith("_"): continue
            for s in songs:
                p = s.get('plays', 0)
                total_plays += p
                all_songs.append(s)
        
        top_songs = sorted(all_songs, key=lambda x: x.get('plays', 0), reverse=True)[:15]
        
        info_row = ctk.CTkFrame(self.stats_frame, fg_color="transparent")
        info_row.pack(fill="x", pady=10)
        
        def make_card(parent, title, val):
            c = ctk.CTkFrame(parent, fg_color=COLORS["card"], corner_radius=10)
            c.pack(side="left", fill="x", expand=True, padx=10)
            ctk.CTkLabel(c, text=title, font=("Arial", 12), text_color=COLORS["text_sub"]).pack(pady=(15,5))
            ctk.CTkLabel(c, text=str(val), font=("Helvetica", 24, "bold"), text_color=COLORS["text"]).pack(pady=(0,15))

        make_card(info_row, "Songs in Bibliothek", len(all_songs))
        make_card(info_row, "Gesamt Wiedergaben", total_plays)
        hours = int((total_plays * 3) / 60)
        make_card(info_row, "Hörzeit (ca.)", f"{hours} Std.")

        ctk.CTkLabel(self.stats_frame, text="🏆 Top 15 Meistgehört", font=("Arial", 18, "bold"), text_color=COLORS["text"], anchor="w").pack(fill="x", pady=(30, 10))
        
        for i, s in enumerate(top_songs):
            row = ctk.CTkFrame(self.stats_frame, fg_color=COLORS["card"])
            row.pack(fill="x", pady=2)
            
            rank = i + 1
            rank_color = COLORS["text_sub"]
            if rank == 1: rank_color = "#FFD700"
            elif rank == 2: rank_color = "#C0C0C0"
            elif rank == 3: rank_color = "#CD7F32"
            
            ctk.CTkLabel(row, text=f"#{rank}", width=40, font=("Arial", 14, "bold"), text_color=rank_color).pack(side="left", padx=10)
            ctk.CTkLabel(row, text=s['title'], font=("Arial", 12), text_color=COLORS["text"], anchor="w").pack(side="left", fill="x", expand=True)
            ctk.CTkLabel(row, text=f"{s.get('plays',0)} Plays", width=100, text_color=COLORS["primary"], anchor="e").pack(side="right", padx=20)

        ctk.CTkButton(self.stats_frame, text="← Zurück zur Bibliothek", fg_color=COLORS["bg"], text_color=COLORS["text"], hover_color=COLORS["hover"], command=self.close_statistics).pack(pady=40)

    # FIX: SAUBERES SCHLIESSEN & NEU AUFBAUEN
    def close_statistics(self):
        if self.stats_frame is not None and self.stats_frame.winfo_exists():
            self.stats_frame.destroy()
        self.stats_frame = None
        
        # Sicherstellen dass alles weg ist
        for widget in self.main.winfo_children():
            widget.pack_forget()
            
        # Sauber neu packen (Reihenfolge erzwingen)
        self.header.pack(fill="x", side="top", anchor="n")
        self.tool_row.pack(fill="x", padx=30, pady=(20, 10), side="top", anchor="n")
        self.song_frame.pack(fill="both", expand=True, padx=20, pady=10, side="top", anchor="n")

    # --- FUNKTIONEN ---
    def toggle_mute(self, event=None):
        if self.is_muted:
            self.player.audio_set_volume(int(self.saved_volume))
            self.vol_slider.set(self.saved_volume)
            self.vol_icon.configure(text="🔊")
            self.is_muted = False
        else:
            self.saved_volume = self.vol_slider.get()
            self.player.audio_set_volume(0)
            self.vol_slider.set(0)
            self.vol_icon.configure(text="🔇")
            self.is_muted = True

    def toggle_time_mode(self, event):
        self.show_remaining_time = not self.show_remaining_time

    def show_shortcuts(self):
        msg = (
            "TASTATURKÜRZEL:\n\n"
            "• Leertaste: Play / Pause\n"
            "• Pfeil Rechts: Nächster Song\n"
            "• Pfeil Links: Vorheriger Song\n"
            "• Strg+F: Suche / Import\n"
            "• Mausrad (auf Slider/Sidebar): Lautstärke\n"
            "• Klick auf Zeit: Umschalten (Verstrichen / Rest)\n"
        )
        messagebox.showinfo("Shortcuts", msg)

    def open_text_import(self):
        dia = ctk.CTkToplevel(self); dia.title("Massen-Import"); dia.geometry("500x500"); dia.attributes('-topmost', True)
        ctk.CTkLabel(dia, text="Füge hier deine Songliste ein (ein Song pro Zeile):", font=("Arial", 12)).pack(pady=10)
        textbox = ctk.CTkTextbox(dia, width=450, height=350); textbox.pack(pady=10); textbox.focus()
        def start():
            raw = textbox.get("1.0", "end"); lines = [l.strip() for l in raw.split("\n") if l.strip()]
            if lines: dia.destroy(); self.process_text_import(lines)
        ctk.CTkButton(dia, text="Import Starten", fg_color=COLORS["primary"], command=start).pack(pady=10)

    def process_text_import(self, lines):
        def _task():
            self.add_btn.configure(state="disabled"); self.status_lbl.configure(text=f"Importiere {len(lines)} Songs...")
            count = 0
            for line in lines:
                clean = re.sub(r'^\d+\.\s*', '', line) 
                self.db[self.current_playlist].append({"title": clean, "url": f"ytsearch1:{clean}", "thumb": None})
                count += 1
            self.save_data_async(); self.after(0, self.update_main_song_list); self.after(0, lambda: self.status_lbl.configure(text=f"{count} hinzugefügt!")); self.after(0, lambda: self.add_btn.configure(state="normal"))
        threading.Thread(target=_task, daemon=True).start()
    
    def quick_clipboard_import(self):
        try:
            text = self.clipboard_get()
            if text:
                self.entry.delete(0, 'end')
                self.entry.insert(0, text)
                self.add_by_search()
        except: messagebox.showerror("Fehler", "Clipboard leer oder nicht lesbar.")

    def get_spotify_token(self):
        if not self.sp_client_id or not self.sp_client_secret: return None
        try:
            auth_str = f"{self.sp_client_id}:{self.sp_client_secret}"
            b64_auth = base64.b64encode(auth_str.encode()).decode()
            r = requests.post("https://accounts.spotify.com/api/token", headers={"Authorization": f"Basic {b64_auth}"}, data={"grant_type": "client_credentials"})
            if r.status_code == 200: return r.json()['access_token']
        except: return None
        return None

    def fetch_spotify_tracks(self, url, token):
        headers = {"Authorization": f"Bearer {token}"}
        tracks = []
        try:
            pl_id = re.search(r'playlist/([a-zA-Z0-9]+)', url).group(1)
            api_url = f"https://api.spotify.com/v1/playlists/{pl_id}/tracks?limit=100"
            while api_url:
                r = requests.get(api_url, headers=headers)
                data = r.json()
                for item in data['items']:
                    track = item['track']
                    if track: tracks.append(f"{track['artists'][0]['name']} - {track['name']}")
                api_url = data.get('next')
                time.sleep(0.1)
        except Exception as e: print(e)
        return tracks

    def add_by_search(self):
        query = self.entry.get()
        if not query: return
        
        if "spotify.com" in query:
            if not self.sp_client_id:
                messagebox.showinfo("Info", "Für Spotify Links brauchst du API Keys.")
                return
            def _sp_task():
                self.status_lbl.configure(text="Spotify API...")
                token = self.get_spotify_token()
                if not token:
                    self.after(0, lambda: messagebox.showerror("Fehler", "Spotify Login fehlgeschlagen."))
                    return
                tracks = self.fetch_spotify_tracks(query, token)
                self.process_text_import(tracks)
            threading.Thread(target=_sp_task, daemon=True).start()
            return

        def _yt_task():
            self.add_btn.configure(state="disabled")
            self.status_lbl.configure(text="YouTube...")
            try:
                with yt_dlp.YoutubeDL({'quiet':True, 'extract_flat':True, 'ignoreerrors':True}) as ydl:
                    sq = query if "http" in query else f"ytsearch1:{query}"
                    info = ydl.extract_info(sq, download=False)
                    if 'entries' in info:
                        for e in info['entries']:
                            if e: self.db[self.current_playlist].append({"title":e['title'], "url":e['url'], "thumb":e.get('thumbnail')})
                    elif 'title' in info:
                        self.db[self.current_playlist].append({"title":info['title'], "url":info['webpage_url'], "thumb":info.get('thumbnail')})
                    self.save_data_async(); self.after(0, self.update_main_song_list)
                    self.after(0, lambda: self.status_lbl.configure(text="Fertig"))
            except: self.after(0, lambda: self.status_lbl.configure(text="Fehler"))
            self.after(0, lambda: self.add_btn.configure(state="normal"))
        threading.Thread(target=_yt_task, daemon=True).start()

    def apply_theme_colors(self, theme_name):
        if theme_name in THEME_PRESETS:
            new_theme = THEME_PRESETS[theme_name]
            COLORS.update(new_theme)

    def change_theme(self, theme_name):
        self.apply_theme_colors(theme_name)
        self.current_theme_name = theme_name
        self.db["_settings"]["theme_name"] = theme_name
        self.save_data_async()
        self.refresh_whole_ui()

    def refresh_whole_ui(self):
        self.configure(fg_color=COLORS["bg"])
        self.sidebar.configure(fg_color=COLORS["sidebar"])
        self.main.configure(fg_color="transparent")
        self.header.configure(fg_color=COLORS["sidebar"])
        self.player_bar.configure(fg_color=COLORS["sidebar"])
        self.logo_label.configure(text_color=COLORS["primary"])
        self.create_pl_btn.configure(fg_color=COLORS["primary"], hover_color=COLORS["primary"])
        self.add_btn.configure(fg_color=COLORS["primary"])
        self.progress.configure(progress_color=COLORS["primary"])
        if self.shuffle: self.shuffle_btn.configure(fg_color=COLORS["primary"])
        if self.repeat != "none": self.repeat_btn.configure(fg_color=COLORS["primary"])
        if self.eq_active_preset != "Normal": self.bass_btn.configure(fg_color=COLORS["primary"])
        self.update_sidebar_ui()
        self.update_main_song_list()

    def toggle_settings_menu(self):
        if not self.settings_visible:
            self.settings_panel.pack(fill="x", padx=15, pady=5, after=self.sep1)
            ctk.CTkLabel(self.settings_panel, text="Modus:", font=("Arial", 11, "bold"), text_color=COLORS["text_sub"]).pack(pady=2)
            ctk.CTkSegmentedButton(self.settings_panel, values=["Dark", "Light"], command=self.change_appearance).pack(pady=5)
            ctk.CTkLabel(self.settings_panel, text="Farb-Design:", font=("Arial", 11, "bold"), text_color=COLORS["text_sub"]).pack(pady=(10,2))
            theme_cb = ctk.CTkComboBox(self.settings_panel, values=list(THEME_PRESETS.keys()), command=self.change_theme)
            theme_cb.set(self.current_theme_name)
            theme_cb.pack(pady=5)
            ctk.CTkLabel(self.settings_panel, text="Spotify API (Optional):", font=("Arial", 11, "bold"), text_color=COLORS["text_sub"]).pack(pady=(10,2))
            self.sp_id_entry = ctk.CTkEntry(self.settings_panel, placeholder_text="Client ID", fg_color=COLORS["bg"]); self.sp_id_entry.pack(fill="x", padx=5, pady=2)
            if self.sp_client_id: self.sp_id_entry.insert(0, self.sp_client_id)
            self.sp_secret_entry = ctk.CTkEntry(self.settings_panel, placeholder_text="Client Secret", show="*", fg_color=COLORS["bg"]); self.sp_secret_entry.pack(fill="x", padx=5, pady=2)
            if self.sp_client_secret: self.sp_secret_entry.insert(0, self.sp_client_secret)
            ctk.CTkButton(self.settings_panel, text="Speichern", height=25, fg_color=COLORS["primary"], command=self.save_settings).pack(pady=5)
            ex_frm = ctk.CTkFrame(self.settings_panel, fg_color="transparent")
            ex_frm.pack(fill="x", pady=5)
            ctk.CTkButton(ex_frm, text="↗ Export", width=100, height=25, fg_color=COLORS["bg"], text_color=COLORS["text"], command=self.export_playlist).pack(side="left", padx=2, expand=True)
            ctk.CTkButton(ex_frm, text="↙ Import", width=100, height=25, fg_color=COLORS["bg"], text_color=COLORS["text"], command=self.import_playlist).pack(side="left", padx=2, expand=True)
            ctk.CTkButton(self.settings_panel, text="Playlist leeren", height=25, fg_color="#666", hover_color="#888", command=self.clear_playlist).pack(pady=5)
            ctk.CTkButton(self.settings_panel, text="Reset App", height=25, fg_color=COLORS["danger"], command=self.reset_app).pack(pady=5)
            self.settings_visible = True
        else:
            for w in self.settings_panel.winfo_children(): w.destroy()
            self.settings_panel.pack_forget(); self.settings_visible = False

    def save_settings(self):
        self.sp_client_id = self.sp_id_entry.get().strip(); self.sp_client_secret = self.sp_secret_entry.get().strip()
        if "_settings" not in self.db: self.db["_settings"] = {}
        self.db["_settings"]["sp_id"] = self.sp_client_id; self.db["_settings"]["sp_secret"] = self.sp_client_secret
        self.save_data_async(); self.toggle_settings_menu()

    def create_playlist(self): n=self.pl_entry.get(); (self.db.update({n:[]}) or self.save_data_async() or self.update_sidebar_ui() or self.pl_entry.delete(0,'end')) if n and n not in self.db else None
    def delete_playlist(self, n): (self.db.pop(n) and self.save_data_async() or self.update_sidebar_ui() or self.update_main_song_list()) if n in self.db and len(self.db)>1 else None
    def update_sidebar_ui(self):
        for w in self.pl_scroll.winfo_children(): w.destroy()
        for name in self.db.keys():
            if name.startswith("_"): continue
            col = COLORS["card"] if name == self.current_playlist else "transparent"
            text_col = COLORS["text"] if name == self.current_playlist else COLORS["text_sub"]
            f = ctk.CTkFrame(self.pl_scroll, fg_color="transparent"); f.pack(fill="x", pady=1)
            ctk.CTkButton(f, text=f"  {name}", anchor="w", fg_color=col, text_color=text_col, height=35, command=lambda n=name: self.switch_pl(n)).pack(side="left", fill="x", expand=True)
            if name != "Favoriten": ctk.CTkButton(f, text="×", width=30, fg_color="transparent", text_color=COLORS["text_sub"], hover_color="#c00", command=lambda n=name: self.delete_playlist(n)).pack(side="right")
    
    def next_page(self):
        songs = self.get_filtered_songs()
        if (self.page + 1) * self.items_per_page < len(songs):
            self.page += 1
            self.update_main_song_list()
    
    def prev_page(self):
        if self.page > 0:
            self.page -= 1
            self.update_main_song_list()

    def update_main_song_list(self):
        for w in self.song_frame.winfo_children(): w.destroy()
        self.drag_data["frames"] = []
        songs = self.get_filtered_songs()
        start_idx = self.page * self.items_per_page
        end_idx = start_idx + self.items_per_page
        current_page_songs = songs[start_idx:end_idx]
        self.page_lbl.configure(text=f"{self.page + 1}")
        if not current_page_songs: 
            ctk.CTkLabel(self.song_frame, text="Keine Songs", text_color=COLORS["text_sub"]).pack(pady=20)
            return
        for i, song in enumerate(current_page_songs):
            abs_index = start_idx + i 
            f = ctk.CTkFrame(self.song_frame, fg_color=COLORS["card"], corner_radius=6, border_width=1, border_color=COLORS["separator"])
            f.pack(fill="x", pady=2, padx=2)
            real_idx = self.db[self.current_playlist].index(song)
            is_active = (real_idx == self.current_index)
            col = COLORS["primary"] if is_active else COLORS["text"]
            is_filter = len(songs) != len(self.db[self.current_playlist])
            cursor = "arrow" if is_filter else "fleur"
            handle = ctk.CTkLabel(f, text="::", width=25, text_color=COLORS["text_sub"], cursor=cursor)
            handle.pack(side="left", padx=5)
            btn = ctk.CTkButton(f, text=song['title'], anchor="w", fg_color="transparent", text_color=col, hover_color=COLORS["hover"], height=35, command=lambda idx=real_idx: self.start_song(idx))
            btn.pack(side="left", fill="x", expand=True)
            btn.bind("<Button-3>", lambda event, idx=i: self.open_context_menu(event, abs_index))
            ctk.CTkButton(f, text="×", width=30, height=30, fg_color="transparent", text_color=COLORS["text_sub"], hover_color="#ff4444", command=lambda idx=real_idx: self.delete_song(idx)).pack(side="right", padx=5)
            if not is_filter: 
                self.drag_data["frames"].append((f, i))
                handle.bind("<ButtonPress-1>", lambda e, idx=i: self.on_drag_start(e, idx))
                handle.bind("<ButtonRelease-1>", self.on_drag_release)

    def start_song(self, idx):
        if not self.db[self.current_playlist]: return
        self.current_index = idx % len(self.db[self.current_playlist])
        s = self.db[self.current_playlist][self.current_index]
        self.mini_title.configure(text=s['title'])
        s['plays'] = s.get('plays', 0) + 1
        if s in self.db[self.current_playlist]: self.current_index = self.db[self.current_playlist].index(s); self.update_main_song_list()
        self.save_data_async()
        def _play():
            try:
                url = s['url']
                if s.get('local'): media = self.instance.media_new(url)
                else:
                    with yt_dlp.YoutubeDL({'format':'bestaudio', 'quiet':True}) as ydl:
                        info = ydl.extract_info(url, download=False)
                        if 'entries' in info: info = info['entries'][0]
                        media = self.instance.media_new(info['url'])
                        if not s.get('thumb'): s['thumb'] = info.get('thumbnail'); self.load_thumb(s)
                self.player.set_media(media); self.player.play()
                try:
                    current_speed = float(self.speed_btn.cget("text").replace("x",""))
                    if current_speed != 1.0: self.player.set_rate(current_speed)
                except: pass
                if not self.is_muted:
                    self.player.audio_set_volume(int(self.vol_slider.get()))
                else:
                    self.player.audio_set_volume(0)
                self.after(0, lambda: self.play_btn.configure(text="⏸"))
            except: pass
        threading.Thread(target=_play, daemon=True).start()
        if not s.get('local'): threading.Thread(target=self.load_thumb, args=(s,), daemon=True).start()
        else: self.load_thumb(s)

    def load_thumb(self, song):
        url = song.get('thumb')
        if not url:
            vid = re.search(r'(?:v=|\/)([0-9A-Za-z_-]{11}).*', song.get('url',''))
            if vid: url = f"https://i.ytimg.com/vi/{vid.group(1)}/mqdefault.jpg"
            else: self.after(0, lambda: self.update_img(None)); return
        fname = hashlib.md5(url.encode()).hexdigest() + ".jpg"
        fpath = os.path.join(self.cache_dir, fname)
        if os.path.exists(fpath):
            try: 
                with open(fpath,"rb") as f: self.after(0, lambda d=f.read(): self.update_img(d)); return
            except: pass
        try:
            r = requests.get(url, timeout=5)
            with open(fpath,"wb") as f: f.write(r.content)
            self.after(0, lambda: self.update_img(r.content))
        except: self.after(0, lambda: self.update_img(None))

    def update_img(self, data):
        if data:
            self.current_cover_data = data
            try: i=ctk.CTkImage(Image.open(BytesIO(data)),size=(60,60)); self.current_image_obj=i; self.mini_img.configure(image=i, text="")
            except: self.mini_img.configure(image=None, text="🎵")
        else: self.mini_img.configure(image=None, text="🎵")

    def play_next(self): 
        if self.queue: s=self.queue.pop(0); (self.start_song(self.db[self.current_playlist].index(s)) if s in self.db[self.current_playlist] else None); return
        if not self.db[self.current_playlist]: return
        n = random.randint(0, len(self.db[self.current_playlist])-1) if self.shuffle else (self.current_index + 1) % len(self.db[self.current_playlist])
        self.start_song(n)
    def play_prev(self): self.start_song(self.current_index-1)
    def toggle_pause(self): (self.player.pause() or self.play_btn.configure(text="▶")) if self.player.is_playing() else (self.player.play() or self.play_btn.configure(text="⏸"))
    def seek_song(self, v): t=self.player.get_length(); self.time_now.configure(text=self.fmt_time(t*(float(v)/1000))) if t>0 else None; self.player.set_position(float(v)/1000)
    def change_volume(self, v): 
        if not self.is_muted:
            self.player.audio_set_volume(int(v))
            self.save_data_async()
    def delete_song(self, i): self.db[self.current_playlist].pop(i); self.save_data_async(); self.update_main_song_list()
    def toggle_shuffle(self): self.shuffle = not self.shuffle; self.shuffle_btn.configure(fg_color=COLORS["primary"] if self.shuffle else COLORS["bg"]); self.save_data_async()
    def toggle_repeat(self): m=["none","one","all"]; self.repeat=m[(m.index(self.repeat)+1)%3]; self.repeat_btn.configure(text=f"🔁 {self.repeat}", fg_color=COLORS["primary"] if self.repeat!="none" else COLORS["bg"]); self.save_data_async()
    def add_local_files(self): fs=filedialog.askopenfilenames(filetypes=[("Audio","*.mp3 *.wav *.m4a")]); [self.db[self.current_playlist].append({"title":os.path.basename(f),"url":f,"thumb":None,"local":True}) for f in fs] if fs else None; self.save_data_async(); self.update_main_song_list()
    def download_current(self):
        if self.current_index==-1: return
        s = self.db[self.current_playlist][self.current_index]
        if s.get("local"): return
        def _dl():
            self.dl_btn.configure(text="⏳", state="disabled")
            try:
                p = os.path.join(self.music_dir, "".join([c for c in s['title'] if c.isalnum() or c in " ._"]).rstrip()+".m4a")
                with yt_dlp.YoutubeDL({'format':'bestaudio[ext=m4a]','outtmpl':p,'quiet':True}) as y: y.download([s['url']])
                self.after(0, lambda: self.dl_btn.configure(text="✅"))
            except: self.after(0, lambda: self.dl_btn.configure(text="❌"))
            time.sleep(2); self.after(0, lambda: self.dl_btn.configure(text="⬇ Save", state="normal"))
        threading.Thread(target=_dl, daemon=True).start()
    def open_lyrics(self): t=self.mini_title.cget("text"); webbrowser.open(f"https://www.google.com/search?q={t.replace(' ','+')}+lyrics") if t!="Kein Song" else None
    def open_music_folder(self): os.startfile(self.music_dir)
    def open_big_view(self, e): 
        if not self.current_image_obj: return
        t=ctk.CTkToplevel(self); t.geometry("500x500"); t.attributes('-topmost',True); ctk.CTkLabel(t,text="",image=ctk.CTkImage(Image.open(BytesIO(self.current_cover_data)),size=(400,400))).pack(pady=20)
    def toggle_mini_player(self): self.attributes('-toolwindow', not self.attributes('-toolwindow')); self.geometry("450x180" if self.attributes('-toolwindow') else "1400x950")
    
    def on_drag_start(self, e, i): self.drag_data["item_idx"]=i
    def on_drag_release(self, e):
        s=self.drag_data["item_idx"]; self.drag_data["item_idx"]=None
        if s is None: return
        m=self.winfo_pointery()
        target_rel = next((i for i,(f,_) in enumerate(self.drag_data["frames"]) if f.winfo_rooty()<=m<=f.winfo_rooty()+f.winfo_height()), None)
        if target_rel is not None and target_rel!=s: 
            start_offset = self.page * self.items_per_page
            abs_source = start_offset + s
            abs_target = start_offset + target_rel
            l=self.db[self.current_playlist]
            l.insert(abs_target, l.pop(abs_source))
            self.save_data_async(); self.update_main_song_list()

    def on_space_press(self, e): self.toggle_pause() if not "entry" in str(self.focus_get()).lower() and not "textbox" in str(self.focus_get()).lower() else None
    def on_right_press(self, e): self.play_next() if not "entry" in str(self.focus_get()).lower() else None
    def on_left_press(self, e): self.play_prev() if not "entry" in str(self.focus_get()).lower() else None
    def on_global_click(self, event):
        try:
            if event.widget.winfo_class() not in ["Entry", "Text"]: self.focus()
        except: pass
    def on_vol_scroll(self, event):
        curr = self.vol_slider.get(); new_val = curr + 5 if event.delta > 0 else curr - 5
        new_val = max(0, min(100, new_val)); self.vol_slider.set(new_val); self.change_volume(new_val)

    def filter_change_event(self, *args): 
        self.page = 0
        self.update_main_song_list()
        
    def get_filtered_songs(self): t=self.filter_var.get().lower(); l=self.db[self.current_playlist]; return [s for s in l if t in s['title'].lower()] if t else l
    def set_dragging(self, v): self.is_slider_dragging=v
    def fmt_time(self, ms): s=int(ms/1000); m,s=divmod(s,60); return f"{m:02d}:{s:02d}"
    def change_appearance(self, m): 
        ctk.set_appearance_mode(m)
        self.db["_settings"]["mode"]=m
        self.save_data_async()
        self.refresh_whole_ui()
        self.toggle_settings_menu(); self.toggle_settings_menu() 

    def reset_app(self): 
        if messagebox.askyesno("Reset", "Alles löschen?"): self.db={"Favoriten":[]}; self.save_data_async(); self.current_playlist="Favoriten"; self.update_sidebar_ui(); self.update_main_song_list()
    
    # --- POPUPS ---
    def open_sort_menu(self):
        if self.sort_popup and self.sort_popup.winfo_exists():
            self.sort_popup.destroy()
            return
        
        self.sort_popup = ctk.CTkFrame(self, width=150, height=110, fg_color="#333", corner_radius=5, border_width=1, border_color="#555")
        x = self.sort_btn.winfo_rootx() - self.winfo_rootx()
        y = self.sort_btn.winfo_rooty() - self.winfo_rooty() + 35
        self.sort_popup.place(x=x, y=y)

        def sort(k, rev=False):
            self.db[self.current_playlist].sort(key=lambda x: x.get(k, 0) if k=='plays' else x[k].lower(), reverse=rev)
            t = self.mini_title.cget("text")
            for i,s in enumerate(self.db[self.current_playlist]):
                if s['title'] == t: self.current_index = i; break
            self.save_data_async(); self.update_main_song_list(); self.sort_popup.destroy()
        
        def dedup():
            seen = set(); new_l = []
            for s in self.db[self.current_playlist]:
                i = s['url']
                if i not in seen: seen.add(i); new_l.append(s)
            diff = len(self.db[self.current_playlist]) - len(new_l)
            self.db[self.current_playlist] = new_l
            self.save_data_async(); self.update_main_song_list(); self.sort_popup.destroy()
            messagebox.showinfo("Info", f"{diff} Duplikate entfernt.")

        ctk.CTkButton(self.sort_popup, text="A-Z", fg_color="transparent", hover_color="#444", command=lambda:sort('title')).pack(fill="x", pady=2)
        ctk.CTkButton(self.sort_popup, text="🔥 Beliebt", fg_color="transparent", hover_color="#444", command=lambda:sort('plays', True)).pack(fill="x", pady=2)
        ctk.CTkButton(self.sort_popup, text="♻ Duplikate", fg_color="transparent", hover_color="#444", command=dedup).pack(fill="x", pady=2)
        self.after(4000, lambda: self.sort_popup.destroy() if self.sort_popup and self.sort_popup.winfo_exists() else None)

    def open_sleep_menu(self):
        if self.sleep_popup and self.sleep_popup.winfo_exists():
            self.sleep_popup.destroy()
            return
            
        self.sleep_popup = ctk.CTkFrame(self, width=150, height=120, fg_color="#333", corner_radius=5, border_width=1, border_color="#555")
        x = self.sleep_btn.winfo_rootx() - self.winfo_rootx() - 100
        y = self.sleep_btn.winfo_rooty() - self.winfo_rooty() + 45
        self.sleep_popup.place(x=x, y=y)
        
        def set_t(min):
            self.sleep_timer_end = time.time()+(min*60)
            self.sleep_btn.configure(text="💤", fg_color=COLORS["primary"])
            self.sleep_popup.destroy()
        def off():
            self.sleep_timer_end = None
            self.sleep_btn.configure(text="🌙", fg_color=COLORS["bg"])
            self.sleep_popup.destroy()
            
        ctk.CTkButton(self.sleep_popup, text="10 Min", fg_color="transparent", hover_color="#444", command=lambda: set_t(10)).pack(fill="x", pady=2)
        ctk.CTkButton(self.sleep_popup, text="30 Min", fg_color="transparent", hover_color="#444", command=lambda: set_t(30)).pack(fill="x", pady=2)
        ctk.CTkButton(self.sleep_popup, text="60 Min", fg_color="transparent", hover_color="#444", command=lambda: set_t(60)).pack(fill="x", pady=2)
        ctk.CTkButton(self.sleep_popup, text="AUS", fg_color="transparent", text_color="red", hover_color="#444", command=off).pack(fill="x", pady=2)
        self.after(4000, lambda: self.sleep_popup.destroy() if self.sleep_popup and self.sleep_popup.winfo_exists() else None)
    
    def open_speed_menu(self):
        if self.speed_popup and self.speed_popup.winfo_exists():
            self.speed_popup.destroy()
            return

        self.speed_popup = ctk.CTkFrame(self, width=120, height=180, fg_color="#333", corner_radius=5, border_width=1, border_color="#555")
        x = self.speed_btn.winfo_rootx() - self.winfo_rootx()
        y = self.speed_btn.winfo_rooty() - self.winfo_rooty() + 35
        self.speed_popup.place(x=x, y=y)

        def set_s(rate):
            self.player.set_rate(rate)
            col = COLORS["primary"] if rate != 1.0 else COLORS["bg"]
            self.speed_btn.configure(text=f"{rate}x", fg_color=col)
            self.speed_popup.destroy()

        speeds = [0.5, 0.8, 1.0, 1.25, 1.5, 2.0]
        for s in speeds:
            lbl = f"{s}x {'(Normal)' if s==1.0 else ''}"
            ctk.CTkButton(self.speed_popup, text=lbl, fg_color="transparent", hover_color="#444", command=lambda r=s: set_s(r)).pack(fill="x", pady=1)

        self.after(5000, lambda: self.speed_popup.destroy() if self.speed_popup and self.speed_popup.winfo_exists() else None)

    def open_eq_menu(self):
        if self.eq_popup and self.eq_popup.winfo_exists():
            self.eq_popup.destroy()
            return

        self.eq_popup = ctk.CTkFrame(self, width=140, height=200, fg_color="#333", corner_radius=5, border_width=1, border_color="#555")
        x = self.bass_btn.winfo_rootx() - self.winfo_rootx()
        y = self.bass_btn.winfo_rooty() - self.winfo_rooty() + 35
        self.eq_popup.place(x=x, y=y)

        def set_eq(name, values):
            for i in range(10):
                self.equalizer.set_amp_at_index(values[i], i)
            self.player.set_equalizer(self.equalizer)
            self.eq_active_preset = name
            col = COLORS["primary"] if name != "Normal" else COLORS["bg"]
            self.bass_btn.configure(fg_color=col)
            self.eq_popup.destroy()

        presets = {
            "Normal":  [0]*10,
            "Bass++":  [12, 10, 8, 5, 2, 0, 0, 0, 0, 0],
            "Rock":    [8, 6, 4, -2, -4, -2, 4, 6, 8, 8],
            "Pop":     [4, 3, 2, 4, 5, 4, 2, 3, 4, 5],
            "Techno":  [10, 8, 5, 0, 0, 0, 4, 8, 10, 10],
            "Klassik": [5, 4, 3, 2, -2, -2, 0, 2, 4, 5]
        }

        for name, vals in presets.items():
            txt_col = COLORS["primary"] if name == self.eq_active_preset else "white"
            ctk.CTkButton(self.eq_popup, text=name, text_color=txt_col, fg_color="transparent", hover_color="#444", command=lambda n=name, v=vals: set_eq(n, v)).pack(fill="x", pady=1)

        self.after(5000, lambda: self.eq_popup.destroy() if self.eq_popup and self.eq_popup.winfo_exists() else None)

    def export_playlist(self):
        f = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")])
        if f:
            try:
                json.dump(self.db[self.current_playlist], open(f, "w"), indent=4)
                messagebox.showinfo("Export", "Playlist gespeichert!")
            except: messagebox.showerror("Fehler", "Konnte nicht speichern.")

    def import_playlist(self):
        f = filedialog.askopenfilename(filetypes=[("JSON", "*.json")])
        if f:
            try:
                data = json.load(open(f))
                if isinstance(data, list):
                    self.db[self.current_playlist].extend(data)
                    self.save_data_async()
                    self.update_main_song_list()
                    messagebox.showinfo("Import", f"{len(data)} Songs hinzugefügt!")
                else: messagebox.showerror("Fehler", "Falsches Format.")
            except: messagebox.showerror("Fehler", "Datei defekt.")

    def clear_playlist(self):
        if messagebox.askyesno("Leeren", "Alle Songs aus dieser Playlist entfernen?"):
            self.db[self.current_playlist] = []
            self.save_data_async(); self.update_main_song_list()

    def open_context_menu(self, e, abs_idx):
        m=ctk.CTkFrame(self,width=150,height=160,fg_color="#333",corner_radius=5); m.place(x=e.x_root-self.winfo_rootx(),y=e.y_root-self.winfo_rooty())
        def cl(): m.destroy()
        def ren(): s=self.get_filtered_songs()[abs_idx]; ri=self.db[self.current_playlist].index(s); d=ctk.CTkInputDialog(text="Titel:", title="Edit"); t=d.get_input(); (self.db[self.current_playlist][ri].update({'title':t}) or self.save_data_async() or self.update_main_song_list() or (self.mini_title.configure(text=t) if ri==self.current_index else None)) if t else None; cl()
        def qa(): self.queue.append(self.get_filtered_songs()[abs_idx]); cl()
        def info(): 
            s = self.get_filtered_songs()[abs_idx]
            cnt = s.get('plays', 0)
            messagebox.showinfo("Statistik", f"Titel: {s['title']}\n\nAbgespielt: {cnt} mal")
            cl()
        
        def fav():
            s = self.get_filtered_songs()[abs_idx]
            if s in self.db["Favoriten"]:
                messagebox.showinfo("Info", "Song ist schon in Favoriten.")
            else:
                self.db["Favoriten"].append(s)
                self.save_data_async()
                if self.current_playlist == "Favoriten": self.update_main_song_list()
                messagebox.showinfo("Info", "Zu Favoriten hinzugefügt!")
            cl()

        # YouTube Link Öffner
        def open_yt():
            s = self.get_filtered_songs()[abs_idx]
            u = s.get('url', '')
            if u.startswith('http'): webbrowser.open(u)
            else: messagebox.showinfo("Info", "Kein Web-Link verfügbar (lokale Datei).")
            cl()

        ctk.CTkButton(m,text="❤️ Zu Favoriten",fg_color="transparent",hover_color="#444",command=fav).pack(fill="x",pady=2)
        ctk.CTkButton(m,text="🌐 Öffne YouTube",fg_color="transparent",hover_color="#444",command=open_yt).pack(fill="x",pady=2)
        ctk.CTkButton(m,text="Umbenennen",fg_color="transparent",hover_color="#444",command=ren).pack(fill="x",pady=2)
        ctk.CTkButton(m,text="In Warteschlange",fg_color="transparent",hover_color="#444",command=qa).pack(fill="x",pady=2)
        ctk.CTkButton(m,text="Info / Statistik",fg_color="transparent",hover_color="#444",command=info).pack(fill="x",pady=2)
        ctk.CTkButton(m,text="Abbrechen",fg_color="transparent",hover_color="#444",text_color="red",command=cl).pack(fill="x",pady=2)
        self.after(4000,cl)
    
    def bg_loop(self):
        while True:
            if self.player.is_playing() and not self.is_slider_dragging:
                p,l=self.player.get_position(), self.player.get_length()
                if l>0:
                    current_time_ms = l * p
                    if self.show_remaining_time:
                        remaining = l - current_time_ms
                        time_str = f"-{self.fmt_time(remaining)}"
                    else:
                        time_str = self.fmt_time(current_time_ms)
                    
                    self.time_now.configure(text=time_str)
                    self.time_total.configure(text=self.fmt_time(l))
                    self.progress.set(p*1000)
            if self.player.get_state()==vlc.State.Ended: self.after(0, self.play_next)
            if self.sleep_timer_end and time.time()>self.sleep_timer_end: self.player.stop(); self.sleep_timer_end=None; self.after(0, lambda: self.sleep_btn.configure(text="🌙", fg_color=COLORS["bg"]))
            time.sleep(0.5)
    
    def load_data(self): return json.load(open(DATA_FILE,"r")) if os.path.exists(DATA_FILE) else {"Favoriten":[]}
    def save_data_async(self): threading.Thread(target=self._save_data_thread, daemon=True).start()
    def _save_data_thread(self):
        with self.data_lock:
            self.db["_session"]={"last_playlist":self.current_playlist,"last_index":self.current_index,"volume":self.vol_slider.get(),"shuffle":self.shuffle,"repeat":self.repeat}
            try: json.dump(self.db, open(DATA_FILE,"w"), indent=4)
            except: pass
    
    # --- FIX: Switch Playlist schließt jetzt Stats ---
    def switch_pl(self, n): 
        if self.stats_frame and self.stats_frame.winfo_exists():
            self.close_statistics()
        self.current_playlist=n; self.save_data_async(); self.update_sidebar_ui(); self.page = 0; self.update_main_song_list()

if __name__ == "__main__":
    app = Bastify()
    app.mainloop()