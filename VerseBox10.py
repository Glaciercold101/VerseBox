"""
Tiny Line Viewer - Borderless v6.1 - 10 themes - Pin & Narration (Fixed save) + Mint Floral & Pink Floral - STRETCH Light (No Pillow)
Added: Narration (TTS) - speaks current verse, auto-narrate on verse change
Offline on Windows via the built-in SAPI/System.Speech voices (no pip needed).
The voice menu includes installed voices such as Microsoft David and Microsoft Zira.
"""

import tkinter as tk
from tkinter import filedialog
import os, json, random, sys, base64, threading, queue, subprocess, re
import tkinter.font as tkfont
from fractions import Fraction
# LIGHT: NO Pillow - Pillow was the 11MB -> 30MB jump.
# Uses Tk's built-in zoom()+subsample() to STRETCH to window. Saves ~15-18MB in the exe.
_HAS_PIL = False
_PILImage = None
_PILImageTk = None

def get_config_path():
    """Obscured config - stored in AppData, not visible next to exe"""
    if sys.platform == 'win32':
        appdata = os.getenv('APPDATA')
        if appdata:
            config_dir = os.path.join(appdata, 'VerseBox')
            os.makedirs(config_dir, exist_ok=True)
            return os.path.join(config_dir, 'settings.dat')
    # Fallback: hidden file in home, no .json extension
    config_dir = os.path.join(os.path.expanduser('~'), '.versebox')
    os.makedirs(config_dir, exist_ok=True)
    return os.path.join(config_dir, '.settings')

CONFIG_FILE = get_config_path()

def _asset_path(name):
    """Find bundled image: PyInstaller _MEIPASS first, then next to .py / .exe.
    Without this, --onefile exe cannot find --add-data images (v8 old loader only checked __file__)."""
    meipass = getattr(sys, '_MEIPASS', None)
    if meipass:
        cand = os.path.join(meipass, name)
        if os.path.exists(cand):
            return cand
    try:
        base = os.path.dirname(os.path.abspath(__file__))
        cand = os.path.join(base, name)
        if os.path.exists(cand):
            return cand
    except:
        pass
    if getattr(sys, 'frozen', False):
        cand = os.path.join(os.path.dirname(sys.executable), name)
        if os.path.exists(cand):
            return cand
    return name

def _encode_config(data: dict) -> str:
    return base64.b64encode(json.dumps(data).encode('utf-8')).decode('utf-8')

def _decode_config(text: str) -> dict:
    try:
        return json.loads(base64.b64decode(text.encode('utf-8')).decode('utf-8'))
    except:
        try:
            return json.loads(text)
        except:
            return {}

def _set_hidden(path):
    """Mark file hidden WITHOUT wiping other attributes (old code used Set=2 which overwrote them)."""
    if sys.platform == 'win32':
        try:
            import ctypes
            FILE_ATTRIBUTE_HIDDEN = 2
            attrs = ctypes.windll.kernel32.GetFileAttributesW(path)
            if attrs != 0xFFFFFFFF:
                if not (attrs & FILE_ATTRIBUTE_HIDDEN):
                    ctypes.windll.kernel32.SetFileAttributesW(path, attrs | FILE_ATTRIBUTE_HIDDEN)
            else:
                ctypes.windll.kernel32.SetFileAttributesW(path, FILE_ATTRIBUTE_HIDDEN)
        except:
            pass

def _migrate_old_config():
    old_paths = [
        os.path.join(os.path.expanduser("~"), ".tiny_line_viewer_borderless_v5.json"),
        os.path.join(os.path.expanduser("~"), ".versebox", "settings.json"),
    ]
    # Also check next to exe/script
    base_dirs = [os.path.dirname(os.path.abspath(__file__))]
    if getattr(sys, 'frozen', False):
        base_dirs.append(os.path.dirname(sys.executable))
    for bd in base_dirs:
        old_paths.append(os.path.join(bd, ".tiny_line_viewer_borderless_v5.json"))
        old_paths.append(os.path.join(bd, "config.json"))
    
    for old_path in old_paths:
        if os.path.exists(old_path) and os.path.abspath(old_path) != os.path.abspath(CONFIG_FILE):
            try:
                with open(old_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                with open(CONFIG_FILE, 'w', encoding='utf-8') as nf:
                    nf.write(_encode_config(data))
                _set_hidden(CONFIG_FILE)
                os.remove(old_path)
                print(f"Migrated old config from {old_path}")
                return data
            except:
                pass
    return None

class BorderlessViewerV5:
    def __init__(self, root):
        self.root = root
        self.root.overrideredirect(False)
        self.borderless = False
        self.root.geometry("600x170+120+120")
        self.root.minsize(220, 110)
        self.root.title("Scripture Flash - Stable")
        
        self.lines = []
        self.index = 0
        self.filepath = None
        self.font_size = 40
        self.opacity = 0.96
        self.root.attributes("-alpha", self.opacity)
        
        self.auto_enabled = False
        self.auto_delay = 6000
        self.auto_job = None
        self.shuffle_enabled = False
        # Smart shuffle: deal every verse once before reshuffling.
        self.shuffle_bag = []
        self.last_shuffle_index = None
        # Recently viewed history stores source, line index and text.
        self.view_history = []
        self.history_position = -1
        self._record_history = True
        self._fit_job = None
        self._fitted_font_size = None
        self.drag_x = self.drag_y = 0
        self.is_pinned = False

        # --- NARRATION ---
        self.narration_enabled = False
        self.narration_auto = False
        self.narration_rate = 175  # wpm, mapped to SAPI rate -10..10
        self.narration_voice_idx = 0
        self.narration_voices = []  # list of (voice name, display name) from Windows SAPI
        self._speak_queue = queue.Queue()
        self._tts_stop = threading.Event()
        self._tts_process = None
        self._tts_engine = None
        self._tts_thread = None
        self._speaking = False
        self._init_tts_engine()
        # --- Robust save state (v6.1 fix) ---
        self._save_job = None
        self._last_save_error_at = 0
        import time as _time_mod
        self._time_mod = _time_mod
        
        # --- THEMES ---
        self.themes = {
            "Original Dark": {
                "root_bg": "#000000", "frame_bg": "#101318", "display_bg": "#101318",
                "text_fg": "#e9edf1", "info_fg": "#6b7280", "counter_fg": "#6b7280",
                "highlight": "#2b3240", "menu_bg": "#151a21", "menu_fg": "#d1d5db",
                "active_bg": "#232b38", "auto_on": "#22c55e", "auto_off": "#101318",
                "glow": "#7dd3fc", "font_family": "Segoe UI"
            },
            "Green Emerald": {
                "root_bg": "#000807", "frame_bg": "#0b1f19", "display_bg": "#0b1f19",
                "text_fg": "#f5e9c9", "info_fg": "#9ca3af", "counter_fg": "#9ca3af",
                "highlight": "#1e3d32", "menu_bg": "#0f2420", "menu_fg": "#e8f5e9",
                "active_bg": "#1a3d35", "auto_on": "#22c55e", "auto_off": "#0b1f19",
                "glow": "#7dd3fc", "font_family": "Segoe UI Semilight"
            },
            "White Marble": {
                "root_bg": "#f0eeea", "frame_bg": "#ffffff", "display_bg": "#ffffff",
                "text_fg": "#d4af37", "info_fg": "#9ca3af", "counter_fg": "#9ca3af",
                "highlight": "#d6d3ce", "menu_bg": "#faf9f7", "menu_fg": "#5a4a2a",
                "active_bg": "#f0e6c8", "auto_on": "#22c55e", "auto_off": "#e5e5e5",
                "glow": "#d4af37", "font_family": "Cormorant Garamond"
            },
            "White Marble (Night)": {
                "root_bg": "#0a0e14", "frame_bg": "#10141c", "display_bg": "#10141c",
                "text_fg": "#e0e6f0", "info_fg": "#7a8494", "counter_fg": "#7a8494",
                "highlight": "#1e2633", "menu_bg": "#131820", "menu_fg": "#d0d8e8",
                "active_bg": "#1c2330", "auto_on": "#7dd3fc", "auto_off": "#10141c",
                "glow": "#a8c5e8", "font_family": "Cormorant Garamond"
            },
            "Mint Floral": {
                # Mint/teal bg - black text (was pink, changed to black for readability).
                "root_bg": "#bfe8e0", "frame_bg": "#dff2ee", "display_bg": "#e8f7f3",
                "text_fg": "#1a1a1a", "info_fg": "#5a7a74", "counter_fg": "#5a7a74",
                "highlight": "#7fd0c0", "menu_bg": "#d6f0eb", "menu_fg": "#1a3a35",
                "active_bg": "#bfe8e0", "auto_on": "#22c55e", "auto_off": "#dff2ee",
                "glow": "#1a1a1a", "font_family": "Cormorant Garamond"
            },
            "Pink Floral": {
                # Blush pink bg - black text (was light-blue, changed to black for readability).
                "root_bg": "#f5c8d2", "frame_bg": "#fde8ee", "display_bg": "#fde8ee",
                "text_fg": "#1a1a1a", "info_fg": "#9a6a78", "counter_fg": "#9a6a78",
                "highlight": "#f5b8c8", "menu_bg": "#fde8ee", "menu_fg": "#4a1f2e",
                "active_bg": "#f5b8c8", "auto_on": "#22c55e", "auto_off": "#fde8ee",
                "glow": "#1a1a1a", "font_family": "Cormorant Garamond"
            },
            "Autumn Sunset": {
                # Golden sunset field - bright centre, black text like mint/pink.
                "root_bg": "#e8b84b", "frame_bg": "#f9e8c0", "display_bg": "#fdeec0",
                "text_fg": "#1a1a1a", "info_fg": "#8a6a2a", "counter_fg": "#8a6a2a",
                "highlight": "#f0c040", "menu_bg": "#f9e8c0", "menu_fg": "#4a2f10",
                "active_bg": "#f0c040", "auto_on": "#22c55e", "auto_off": "#f9e8c0",
                "glow": "#1a1a1a", "font_family": "Cormorant Garamond"
            },
            "Navy Gold Floral": {
                # Dark navy + gold flowers - white verse, gold info (black would vanish).
                "root_bg": "#0a1428", "frame_bg": "#0f1e3a", "display_bg": "#0f1e3a",
                "text_fg": "#ffffff", "info_fg": "#d4af37", "counter_fg": "#d4af37",
                "highlight": "#1e2f4a", "menu_bg": "#0f1e3a", "menu_fg": "#e8dcc0",
                "active_bg": "#1e2f4a", "auto_on": "#22c55e", "auto_off": "#0f1e3a",
                "glow": "#ffd700", "font_family": "Cormorant Garamond"
            },
            "Red Scroll": {
                # Red scroll + roses - white verse (black on red is low contrast).
                "root_bg": "#5a0a0a", "frame_bg": "#b01010", "display_bg": "#c02020",
                "text_fg": "#ffffff", "info_fg": "#ffd9d9", "counter_fg": "#ffd9d9",
                "highlight": "#e04040", "menu_bg": "#7a0a0a", "menu_fg": "#ffe0e0",
                "active_bg": "#a01010", "auto_on": "#22c55e", "auto_off": "#b01010",
                "glow": "#ffffff", "font_family": "Cormorant Garamond"
            },
            "Navy Glory": {
                # Dark navy + sparkles - white verse, light-blue info.
                "root_bg": "#050a1a", "frame_bg": "#0a1230", "display_bg": "#0a1230",
                "text_fg": "#ffffff", "info_fg": "#a8c5e8", "counter_fg": "#a8c5e8",
                "highlight": "#1a2a4a", "menu_bg": "#0a1230", "menu_fg": "#d0d8e8",
                "active_bg": "#1a2a4a", "auto_on": "#7dd3fc", "auto_off": "#0a1230",
                "glow": "#ffffff", "font_family": "Cormorant Garamond"
            }
            }
    
        self.current_theme = "Original Dark"
        
        # Load background images - LIGHT: Tk only + _asset_path (no Pillow)
        # Mint/Pink PNGs are 1200x340 = exactly 2x of 600x170, so subsample(2,2) fits perfectly.
        self.emerald_img = None
        self.marble_img = None
        self.night_img = None
        self.mint_img = None
        self.pink_img = None
        self.sunset_img = None
        self.navy_gold_img = None
        self.red_scroll_img = None
        self.navy_glory_img = None
        self._bg_src = {}
        self._bg_fitted = None
        self._bg_resize_job = None
        self._bg_last_size = (0, 0)
        try:
            for theme_name, fname, attr in [
                ("Green Emerald", "emerald_bg.png", "emerald_img"),
                ("White Marble", "marble_bg.png", "marble_img"),
                ("White Marble (Night)", "marble_night.png", "night_img"),
                ("Steel", "steel_dash.png", "steel_img"),
                ("Mint Floral", "mint_bg.png", "mint_img"),
                ("Pink Floral", "pink_bg.png", "pink_img"),
                ("Autumn Sunset", "sunset_bg.png", "sunset_img"),
                ("Navy Gold Floral", "navy_gold_bg.png", "navy_gold_img"),
                ("Red Scroll", "red_scroll_bg.png", "red_scroll_img"),
                ("Navy Glory", "navy_glory_bg.png", "navy_glory_img"),
            ]:
                path = _asset_path(fname)
                if os.path.exists(path):
                    try:
                        img = tk.PhotoImage(file=path)
                        self._bg_src[theme_name] = img
                        setattr(self, attr, img)
                    except Exception as e:
                        print(f"Image load error {fname}:", e)
        except Exception as e:
            print("Image load error:", e)

        self.root.configure(bg=self.themes[self.current_theme]["root_bg"])
        self.setup_ui()
        self.load_config()
        self.bind_keys()
        self.apply_theme(self.current_theme)
        if self.lines:
            self.show_line()
            if self.auto_enabled:
                self.schedule_auto()

    # ... rest of methods unchanged from your file ...
    def center_window(self):
        self.root.update_idletasks()
        w, h = 600, 170
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = (sw - w)//2
        y = (sh - h)//2
        self.root.geometry(f"{w}x{h}+{x}+{y}")

    def toggle_borderless(self):
        self.borderless = not self.borderless
        self.root.overrideredirect(self.borderless)
        self.root.withdraw()
        self.root.after(15, self._restore_window)

    def _restore_window(self):
        self.root.deiconify(); self.root.lift(); self.root.focus_force()

    def setup_ui(self):
        t = self.themes[self.current_theme]
        self.frame = tk.Frame(self.root, bg=t["frame_bg"], bd=0, highlightthickness=1, highlightbackground=t["highlight"])
        self.frame.pack(fill="both", expand=True, padx=2, pady=2)
        
        self.display = tk.Label(self.frame, text="Right-click â†’ Open .txt\nCtrl+C=Copy â€¢ R=Random â€¢ S=Shuffle",
            font=(t["font_family"], self.font_size), wraplength=560, justify="center",
            bg=t["display_bg"], fg=t["text_fg"], padx=28, pady=28)
        self.display.pack(fill="both", expand=True)
        self.display.bind("<Configure>", self._schedule_fit_display)
        # Refit bg on resize so flowers stay visible
        try:
            self.display.bind("<Configure>", lambda e: (self._schedule_fit_display(), self._refresh_bg_image()), add="+")
        except:
            pass
        
        self.info = tk.Label(self.frame, text="", font=(t["font_family"], 9), bg=t["display_bg"], fg=t["info_fg"], anchor="w")
        self.info.place(x=8, y=6)
        self.counter = tk.Label(self.frame, text="", font=(t["font_family"], 9), bg=t["display_bg"], fg=t["counter_fg"], anchor="e")
        self.counter.place(relx=1.0, x=-8, y=6, anchor="ne")
        self.auto_dot = tk.Label(self.frame, text="●", font=("Segoe UI", 14, "bold"), fg=t["auto_off"], bd=0, highlightthickness=0)
        self.auto_dot.place(relx=1.0, rely=1.0, x=-10, y=-8, anchor="se")

        # Pin / Lock button - bottom left, obscured config feature
        self.pin_btn = tk.Label(self.frame, text="📌", font=("Segoe UI", 11), fg=t["info_fg"],
                                bg=t["display_bg"], bd=0, cursor="hand2")
        self.pin_btn.place(x=8, rely=1.0, y=-8, anchor="sw")
        self.pin_btn.bind("<Button-1>", lambda e: self.toggle_pin())
        self.pin_btn.bind("<Enter>", self.on_pin_enter)
        self.pin_btn.bind("<Leave>", self.on_pin_leave)

        # Narration button - bottom left, next to pin
        self.narration_btn = tk.Label(self.frame, text="🔇", font=("Segoe UI", 11), fg=t["info_fg"],
                                bg=t["display_bg"], bd=0, cursor="hand2")
        self.narration_btn.place(x=32, rely=1.0, y=-8, anchor="sw")
        self.narration_btn.bind("<Button-1>", lambda e: self.toggle_narration())
        self.narration_btn.bind("<Enter>", self.on_narration_enter)
        self.narration_btn.bind("<Leave>", self.on_narration_leave)
        
        for w in (self.display, self.frame):
            w.bind("<ButtonPress-1>", self.start_drag)
            w.bind("<B1-Motion>", self.do_drag)
        self.display.bind("<Button-1>", lambda e: self.next_line())
        self.display.bind("<Double-Button-1>", lambda e: self.copy_text())
        self.display.bind("<Button-3>", self.show_menu)
        self.display.bind("<MouseWheel>", self.on_wheel)
        self.root.bind("<Button-4>", lambda e: self.prev_line())
        self.root.bind("<Button-5>", lambda e: self.next_line())
        
        self.menu = tk.Menu(self.root, tearoff=0, bg=t["menu_bg"], fg=t["menu_fg"], activebackground=t["active_bg"], bd=0)
        self.menu.add_command(label="Open Bible .txt...", command=self.open_file, accelerator="Ctrl+O")
        self.menu.add_separator()
        self.menu.add_command(label="Copy Verse", command=self.copy_text, accelerator="Ctrl+C")
        self.menu.add_command(label="Back to Previous Verse", command=self.go_back)
        self.menu.add_command(label="Recently Viewed (last 50)...", command=self.show_history)
        self.menu.add_separator()
        self.auto_var = tk.BooleanVar(value=False)
        self.menu.add_checkbutton(label="Auto-advance", variable=self.auto_var, command=self.toggle_auto)
        speed_menu = tk.Menu(self.menu, tearoff=0, bg=t["menu_bg"], fg=t["menu_fg"])
        for label, ms in [("3 sec",3000),("6 sec",6000),("10 sec",10000),("15 sec",15000),("30 sec",30000)]:
            speed_menu.add_command(label=label, command=lambda m=ms: self.set_speed(m))
        self.menu.add_cascade(label="Auto speed", menu=speed_menu)
        self.shuffle_var = tk.BooleanVar(value=False)
        self.menu.add_checkbutton(label="Shuffle mode", variable=self.shuffle_var, command=self.toggle_shuffle, accelerator="S")
        self.menu.add_separator()
        self.menu.add_command(label="Previous (<--)", command=self.prev_line)
        self.menu.add_command(label="Next (-->)", command=self.next_line)
        self.menu.add_command(label="Random Verse", command=self.random_verse, accelerator="R")
        self.menu.add_separator()
        self.menu.add_command(label="Font Larger", command=lambda: self.change_font(2), accelerator="Ctrl+Up")
        self.menu.add_command(label="Font Smaller", command=lambda: self.change_font(-2), accelerator="Ctrl+Down")
        self.menu.add_separator()
        self.top_var = tk.BooleanVar(value=True)
        self.menu.add_checkbutton(label="Always on Top", variable=self.top_var, command=self.toggle_top)
        self.pin_var = tk.BooleanVar(value=False)
        self.menu.add_command(label="📌 Pin Position (Lock)", command=self.toggle_pin)
        self.menu.add_command(label="Toggle Borderless", command=self.toggle_borderless, accelerator="F11")
        self.menu.add_command(label="Opacity +", command=lambda: self.change_opacity(0.05), accelerator="Ctrl+Right")
        self.menu.add_command(label="Opacity -", command=lambda: self.change_opacity(-0.05), accelerator="Ctrl+Left")
        self.menu.add_separator()
        self.theme_var = tk.StringVar(value=self.current_theme)
        theme_menu = tk.Menu(self.menu, tearoff=0, bg=t["menu_bg"], fg=t["menu_fg"])
        for name in self.themes.keys():
            theme_menu.add_radiobutton(label=name, variable=self.theme_var, value=name, command=lambda n=name: self.apply_theme(n))
        self.menu.add_cascade(label="Themes", menu=theme_menu)
        self.menu.add_separator()
        # --- NARRATION MENU ---
        self.narration_var = tk.BooleanVar(value=False)
        self.menu.add_checkbutton(label="Narration On", variable=self.narration_var, command=self.toggle_narration)
        self.narration_auto_var = tk.BooleanVar(value=False)
        self.menu.add_checkbutton(label="Auto-narrate on verse change", variable=self.narration_auto_var, command=self.toggle_auto_narrate)
        self.menu.add_command(label="Speak Verse", command=lambda: self.speak_current(force=True), accelerator="N")
        self.menu.add_command(label="Stop Narration", command=self.stop_narration)
        rate_menu = tk.Menu(self.menu, tearoff=0, bg=t["menu_bg"], fg=t["menu_fg"])
        for label, rate in [("Slow", 125), ("Normal", 175), ("Fast", 225)]:
            rate_menu.add_command(label=label, command=lambda r=rate: self.set_narration_rate(r))
        self.menu.add_cascade(label="Narration Speed", menu=rate_menu)
        self.voice_menu = tk.Menu(self.menu, tearoff=0, bg=t["menu_bg"], fg=t["menu_fg"])
        self.menu.add_cascade(label="Narration Voice", menu=self.voice_menu)
        self._rebuild_voice_menu()
        self.menu.add_separator()
        self.menu.add_command(label="Close", command=self.close_app)

    def _get_fitted_bg(self, theme_name):
        """STRETCH bg to fit window WITHOUT Pillow - Tk only, keeps exe ~12MB.
        Trick: Tk can't do smooth resize, but zoom(x,y) + subsample(x,y) can do fractions.
        e.g. scale 0.75 = zoom 3 / subsample 4, scale 1.5 = zoom 3 / subsample 2.
        We do X and Y separately, so it stretches (not just shrinks uniformly).
        Result is near-exact (within a few px) - Pillow would be pixel-perfect but +18MB.
        """
        if theme_name not in self._bg_src:
            return None
        try:
            w = self.display.winfo_width()
            h = self.display.winfo_height()
            if w < 100 or h < 50:
                w, h = 600, 170
            if self._bg_fitted is not None and self._bg_last_size == (w, h) and getattr(self, '_bg_fitted_theme', None) == theme_name:
                return self._bg_fitted
            src = self._bg_src[theme_name]
            sw, sh = src.width(), src.height()
            def _frac(scale):
                # Best fraction with denominator <=4, numerator capped to keep intermediate sane
                f = Fraction(scale).limit_denominator(4)
                if f.numerator > 6 or f.denominator > 6:
                    # Fallback to nearest integer factor
                    n = max(1, round(scale)) if scale >= 1 else 1
                    d = max(1, round(1/scale)) if scale < 1 else 1
                    return n, d
                return f.numerator, f.denominator
            zx, sx = _frac(w / max(1, sw))
            zy, sy = _frac(h / max(1, sh))
            fitted = src
            # Only zoom if needed, keep intermediate size sane (avoid 8000px blow-up)
            if (zx != 1 or zy != 1):
                if sw * zx <= 4000 and sh * zy <= 2000:
                    fitted = fitted.zoom(zx, zy)
                else:
                    # Too big - fall back to integer subsample only
                    fitted = fitted.subsample(max(1, sx), max(1, sy))
                    self._bg_fitted = fitted
                    self._bg_last_size = (w, h)
                    self._bg_fitted_theme = theme_name
                    return fitted
            if (sx != 1 or sy != 1):
                fitted = fitted.subsample(sx, sy)
            self._bg_fitted = fitted
            self._bg_last_size = (w, h)
            self._bg_fitted_theme = theme_name
            return fitted
        except Exception as e:
            print("bg fit error:", e)
            return None

    def _refresh_bg_image(self, event=None):
        # Called on window resize - debounce 60ms so dragging doesn't lag
        if not hasattr(self, 'display') or not self.display.winfo_exists():
            return
        try:
            if getattr(self, '_bg_resize_job', None) is not None:
                self.root.after_cancel(self._bg_resize_job)
        except:
            pass
        def _do():
            self._bg_resize_job = None
            if self.current_theme in getattr(self, '_bg_src', {}):
                fitted = self._get_fitted_bg(self.current_theme)
                if fitted is not None:
                    try:
                        self.display.configure(image=fitted, compound="center")
                    except:
                        pass
        try:
            self._bg_resize_job = self.root.after(60, _do)
        except:
            _do()

    def apply_theme(self, name):
        self.current_theme = name
        t = self.themes[name]
        self.theme_var.set(name)
        self.root.configure(bg=t["root_bg"])
        self.frame.configure(bg=t["frame_bg"], highlightbackground=t["highlight"])
        # Fitted image selection - uses PIL resized-to-window, falls back to old PhotoImage
        fitted = self._get_fitted_bg(name) if hasattr(self, '_bg_src') else None
        if fitted is not None:
            self.display.configure(image=fitted, compound="center")
        elif name == "Green Emerald" and self.emerald_img:
            self.display.configure(image=self.emerald_img, compound="center")
        elif name == "White Marble" and self.marble_img:
            self.display.configure(image=self.marble_img, compound="center")
        elif name == "White Marble (Night)" and self.night_img:
            self.display.configure(image=self.night_img, compound="center")
        elif name == "Mint Floral" and self.mint_img:
            self.display.configure(image=self.mint_img, compound="center")
        elif name == "Pink Floral" and self.pink_img:
            self.display.configure(image=self.pink_img, compound="center")
        else:
            self.display.configure(image="", compound="none")
        self.display.configure(bg=t["display_bg"], fg=t["text_fg"], font=(t["font_family"], self.font_size))
        try:
            self.back_btn.configure(bg=t["display_bg"], fg=t["info_fg"])
        except Exception:
            pass
        self._schedule_fit_display()
        self.info.configure(bg=t["display_bg"], fg=t["info_fg"], font=(t["font_family"], 9))
        self.counter.configure(bg=t["display_bg"], fg=t["counter_fg"], font=(t["font_family"], 9))
        self.auto_dot.configure(bg=t["display_bg"], fg=t["auto_on"] if self.auto_enabled else t["auto_off"])
        try:
            self.menu.configure(bg=t["menu_bg"], fg=t["menu_fg"], activebackground=t["active_bg"])
        except: pass
        # Update pin + narration button bg/fg to match theme
        try:
            self.pin_btn.configure(bg=t["display_bg"])
            if not self.is_pinned:
                self.pin_btn.configure(fg=t["info_fg"])
            self.update_pin_visual()
        except:
            pass
        try:
            self.narration_btn.configure(bg=t["display_bg"])
            self.update_narration_visual()
        except:
            pass
        self.save_config()

    def bind_keys(self):
        self.root.bind("<space>", lambda e: self.next_line())
        self.root.bind("<Right>", lambda e: self.next_line())
        self.root.bind("<Left>", lambda e: self.prev_line())
        self.root.bind("<Down>", lambda e: self.next_line())
        self.root.bind("<Up>", lambda e: self.prev_line())
        self.root.bind("<r>", lambda e: self.random_verse())
        self.root.bind("<R>", lambda e: self.random_verse())
        self.root.bind("<s>", lambda e: self.toggle_shuffle())
        self.root.bind("<S>", lambda e: self.toggle_shuffle())
        self.root.bind("<Control-c>", lambda e: self.copy_text())
        self.root.bind("<Control-C>", lambda e: self.copy_text())
        self.root.bind("<Escape>", lambda e: self.close_app())
        self.root.bind("<Control-o>", lambda e: self.open_file())
        self.root.bind("<F11>", lambda e: self.toggle_borderless())
        self.root.bind("<Control-Up>", lambda e: self.change_font(2))
        self.root.bind("<Control-Down>", lambda e: self.change_font(-2))
        self.root.bind("<Control-Right>", lambda e: self.change_opacity(0.05))
        self.root.bind("<Control-Left>", lambda e: self.change_opacity(-0.05))
        self.root.bind("<Control-Key-1>", lambda e: self.apply_theme("Original Dark"))
        self.root.bind("<Control-Key-2>", lambda e: self.apply_theme("Green Emerald"))
        self.root.bind("<Control-Key-3>", lambda e: self.apply_theme("White Marble"))
        self.root.bind("<Control-Key-4>", lambda e: self.apply_theme("White Marble (Night)"))
        self.root.bind("<Control-Key-5>", lambda e: self.apply_theme("Mint Floral"))
        self.root.bind("<Control-Key-6>", lambda e: self.apply_theme("Pink Floral"))
        self.root.bind("<Control-Key-7>", lambda e: self.apply_theme("Autumn Sunset"))
        self.root.bind("<Control-Key-8>", lambda e: self.apply_theme("Navy Gold Floral"))
        self.root.bind("<Control-Key-9>", lambda e: self.apply_theme("Red Scroll"))
        self.root.bind("<Control-Key-0>", lambda e: self.apply_theme("Navy Glory"))
        self.root.bind("<n>", lambda e: self.speak_current(force=True))
        self.root.bind("<N>", lambda e: self.speak_current(force=True))
        self.root.bind("<Control-n>", lambda e: self.toggle_auto_narrate())
        self.root.bind("<Control-N>", lambda e: self.toggle_auto_narrate())
        
    def start_drag(self, e):
        if self.is_pinned:
            return
        self.drag_x, self.drag_y = e.x, e.y

    def do_drag(self, e):
        if self.is_pinned:
            return
        self.root.geometry(f"+{self.root.winfo_x()+e.x-self.drag_x}+{self.root.winfo_y()+e.y-self.drag_y}")

    def on_wheel(self, e): self.prev_line() if e.delta>0 else self.next_line()

    def get_pin_menu_label(self):
        return "📍 Unpin Position" if self.is_pinned else "📌 Pin Position (Lock)"

    def toggle_pin(self):
        self.is_pinned = not self.is_pinned
        self.pin_var.set(self.is_pinned)
        self.update_pin_visual()
        self.save_config()

    def update_pin_visual(self):
        # Clean look - only pin icon changes, no red border
        t = self.themes[self.current_theme]
        if self.is_pinned:
            self.pin_btn.config(text="📍", fg="#ff5c5c")
        else:
            self.pin_btn.config(text="📌", fg=t["info_fg"])
        # update menu label if exists
        try:
            for i in range(self.menu.index('end')+1):
                try:
                    lbl = self.menu.entrycget(i, 'label')
                    if 'Pin Position' in lbl or 'Unpin Position' in lbl:
                        self.menu.entryconfig(i, label=self.get_pin_menu_label())
                except:
                    continue
        except:
            pass

    def on_pin_enter(self, e):
        self.pin_btn.config(fg="#ff8787" if self.is_pinned else "#ffffff")

    def on_pin_leave(self, e):
        t = self.themes[self.current_theme]
        self.pin_btn.config(fg="#ff5c5c" if self.is_pinned else t["info_fg"])

    def show_menu(self, e):
        # Refresh narration voice list (in case voices changed)
        try:
            self._rebuild_voice_menu()
        except:
            pass
        # Update pin label dynamically before showing
        try:
            for i in range(self.menu.index('end')+1):
                try:
                    lbl = self.menu.entrycget(i, 'label')
                    if 'Pin Position' in lbl or 'Unpin Position' in lbl:
                        self.menu.entryconfig(i, label=self.get_pin_menu_label())
                except:
                    continue
        except:
            pass
        self.menu.tk_popup(e.x_root, e.y_root)
    
    def open_file(self):
        path = filedialog.askopenfilename(title="Open .txt", filetypes=[("Text","*.txt"),("All","*.*")])
        if not path: return
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            self.lines = [l.rstrip("\n") for l in f if l.strip()]
        self.filepath = path
        self.index = 0
        self.shuffle_bag = []
        self.last_shuffle_index = None
        self.info.config(text=os.path.basename(path))
        self.show_line()

    def show_line(self, record_history=True):
        if not self.lines: return
        self.display.config(text=self.lines[self.index].strip())
        self.counter.config(text=f"{self.index+1} / {len(self.lines)}")
        self._schedule_fit_display()
        if record_history and self._record_history:
            entry = {"file": self.filepath, "index": self.index, "text": self.lines[self.index].strip()}
            if not self.view_history or (self.view_history[-1].get("file"), self.view_history[-1].get("index")) != (entry["file"], entry["index"]):
                if self.history_position < len(self.view_history) - 1:
                    self.view_history = self.view_history[:self.history_position + 1]
                self.view_history.append(entry)
                self.view_history = self.view_history[-50:]
            self.history_position = len(self.view_history) - 1
        self.save_config()
        if self.narration_auto and self.narration_enabled:
            self.speak_current()
        if self.auto_enabled: self.schedule_auto()

    def next_line(self):
        if not self.lines: return
        self.index = (self.index + 1) % len(self.lines); self.show_line()
    def prev_line(self):
        if not self.lines: return
        self.index = (self.index - 1) % len(self.lines); self.show_line()
        
    def _next_shuffle_index(self):
        if len(self.lines) <= 1:
            return 0
        if not self.shuffle_bag:
            self.shuffle_bag = [i for i in range(len(self.lines)) if i != self.index]
            random.shuffle(self.shuffle_bag)
            # The first item of a new cycle must not repeat the last item.
            if self.last_shuffle_index is not None and self.shuffle_bag and self.shuffle_bag[-1] == self.last_shuffle_index:
                self.shuffle_bag[0], self.shuffle_bag[-1] = self.shuffle_bag[-1], self.shuffle_bag[0]
        chosen = self.shuffle_bag.pop()
        self.last_shuffle_index = chosen
        return chosen

    def random_verse(self):
        if not self.lines: return
        if len(self.lines) > 1:
            self.index = self._next_shuffle_index()
        else:
            self.index = 0
        self.show_line()
        t = self.themes[self.current_theme]
        self.display.config(fg=t["glow"])
        self.root.after(350, lambda: self.display.config(fg=t["text_fg"]))
        
    def copy_text(self):
        if not self.lines: return
        text = self.lines[self.index].strip()
        self.root.clipboard_clear(); self.root.clipboard_append(text)
        t = self.themes[self.current_theme]
        original = self.info.cget("text")
        self.info.config(text="Copied!", fg="#22c55e")
        self.root.after(800, lambda: self.info.config(text=original, fg=t["info_fg"]))
        
    def toggle_auto(self):
        self.auto_enabled = not self.auto_enabled
        self.auto_var.set(self.auto_enabled)
        t = self.themes[self.current_theme]
        self.auto_dot.config(fg=t["auto_on"] if self.auto_enabled else t["auto_off"])
        if self.auto_enabled: self.schedule_auto()
        else: self.cancel_auto()
        self.save_config()
            
    def toggle_shuffle(self):
        self.shuffle_enabled = not self.shuffle_enabled
        self.shuffle_bag = []
        self.last_shuffle_index = None
        self.shuffle_var.set(self.shuffle_enabled)
        self.info.config(text=f"{os.path.basename(self.filepath) if self.filepath else ''} {'[SHUFFLE]' if self.shuffle_enabled else ''}".strip())
        self.save_config()
        
    def schedule_auto(self):
        self.cancel_auto()
        if self.auto_enabled and self.lines:
            self.auto_job = self.root.after(self.auto_delay, self.auto_step)
    def cancel_auto(self):
        if self.auto_job: self.root.after_cancel(self.auto_job); self.auto_job = None
    def auto_step(self):
        self.random_verse() if self.shuffle_enabled else self.next_line()
        
    def set_speed(self, ms): self.auto_delay = ms; self.save_config()
    def change_font(self, d):
        self.font_size = max(14, min(56, self.font_size+d))
        self._schedule_fit_display()
        t = self.themes[self.current_theme]
        self.info.config(text=f"Maximum font {self.font_size}pt", fg=t["glow"])
        self.root.after(800, lambda: self.info.config(text=os.path.basename(self.filepath) if self.filepath else "", fg=t["info_fg"]))
        self.save_config()

    def _schedule_fit_display(self, event=None):
        if self._fit_job is None:
            try:
                self._fit_job = self.root.after_idle(self._fit_display)
            except tk.TclError:
                self._fit_job = None

    def _fit_display(self):
        self._fit_job = None
        if not hasattr(self, "display") or not self.display.winfo_exists():
            return
        width = max(80, self.display.winfo_width() - 56)
        height = max(40, self.display.winfo_height() - 56)
        try:
            self.display.configure(wraplength=width)
            content = self.display.cget("text") or " "
            t = self.themes[self.current_theme]
            chosen = 14
            for size in range(self.font_size, 13, -1):
                f = tkfont.Font(family=t["font_family"], size=size)
                lines = 0
                for paragraph in content.split("\n"):
                    if not paragraph:
                        lines += 1
                        continue
                    line_width = 0
                    paragraph_lines = 1
                    for word in paragraph.split():
                        word_width = f.measure(word + " ")
                        if line_width and line_width + word_width > width:
                            paragraph_lines += 1
                            line_width = word_width
                        else:
                            line_width += word_width
                    lines += paragraph_lines
                if lines * f.metrics("linespace") <= height:
                    chosen = size
                    break
            if chosen != self._fitted_font_size:
                self.display.configure(font=(t["font_family"], chosen))
                self._fitted_font_size = chosen
        except tk.TclError:
            pass

    def go_back(self):
        if self.history_position <= 0:
            return
        self.history_position -= 1
        self._restore_history_entry(self.view_history[self.history_position])

    def _restore_history_entry(self, entry):
        path = entry.get("file")
        if path and path != self.filepath and os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8", errors="replace") as f:
                    self.lines = [line.rstrip("\n") for line in f if line.strip()]
                self.filepath = path
            except OSError:
                return
        if path == self.filepath and self.lines:
            idx = entry.get("index", 0)
            if 0 <= idx < len(self.lines):
                self.index = idx
            else:
                self.lines = [entry.get("text", "")]
                self.index = 0
        else:
            self.lines = [entry.get("text", "")]
            self.filepath = path
            self.index = 0
        self.info.config(text=os.path.basename(self.filepath) if self.filepath else "Recently viewed")
        self.show_line(record_history=False)
        self.save_config()

    def show_history(self):
        if not self.view_history:
            self.info.config(text="No recently viewed verses yet")
            return
        win = tk.Toplevel(self.root)
        win.title("Recently Viewed — Last 50")
        win.geometry("520x360")
        win.transient(self.root)
        t = self.themes[self.current_theme]
        win.configure(bg=t["frame_bg"])
        listing = tk.Listbox(win, bg=t["menu_bg"], fg=t["menu_fg"],
                             selectbackground=t["active_bg"], font=(t["font_family"], 10),
                             activestyle="none", bd=0, highlightthickness=0)
        listing.pack(fill="both", expand=True, padx=10, pady=10)
        entries = list(enumerate(self.view_history))
        entries.reverse()
        for _, item in entries:
            source = os.path.basename(item.get("file") or "Current text")
            verse = re.sub(r"\\s+", " ", item.get("text", "")).strip()
            label = f"{source}  |  {verse}"
            listing.insert("end", label[:240])

        def open_selected(event=None):
            selection = listing.curselection()
            if not selection:
                return
            history_idx = entries[selection[0]][0]
            self.history_position = history_idx
            self._restore_history_entry(self.view_history[history_idx])
            win.destroy()
        listing.bind("<Double-Button-1>", open_selected)
        listing.bind("<Return>", open_selected)
        listing.focus_set()
    def toggle_top(self): self.root.attributes("-topmost", self.top_var.get()); self.save_config()
    def change_opacity(self, d):
        self.opacity = max(0.4, min(1.0, self.opacity+d))
        self.root.attributes("-alpha", self.opacity)
        t = self.themes[self.current_theme]
        self.info.config(text=f"Opacity {int(self.opacity*100)}%", fg=t["glow"])
        self.root.after(800, lambda: self.info.config(text=os.path.basename(self.filepath) if self.filepath else "", fg=t["info_fg"]))
        self.save_config()
    def close_app(self):
        try:
            if self._save_job is not None:
                self.root.after_cancel(self._save_job)
                self._save_job = None
        except:
            pass
        self.cancel_auto(); self.stop_narration(); self._shutdown_tts(); self.save_config(force=True); self.root.destroy()
        

    # ================= NARRATION =================
    def _init_tts_engine(self):
        """Use the Windows SAPI voice system directly; no third-party TTS package is needed."""
        self._tts_engine = None
        self.narration_voices = self._get_sapi_voices()
        # Prefer the familiar embedded Windows voices when both are installed.
        preferred = ["zira", "david"]
        for wanted in preferred:
            for idx, (_, name) in enumerate(self.narration_voices):
                if wanted in name.lower():
                    self.narration_voice_idx = idx
                    break
            else:
                continue
            break
        self._tts_thread = threading.Thread(target=self._tts_worker, daemon=True)
        self._tts_thread.start()

    def _get_sapi_voices(self):
        """Return installed Windows SAPI voice names.

        PyInstaller's --noconsole builds can have a different PATH and text
        encoding environment than the Python interpreter. Registry lookup is
        therefore the primary path; PowerShell is only a fallback.
        """
        if sys.platform != "win32":
            return []
        voices = []
        try:
            import winreg
            registry_paths = [
                (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Speech\Voices\Tokens"),
                (winreg.HKEY_CURRENT_USER, r"SOFTWARE\Microsoft\Speech\Voices\Tokens"),
                (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Speech_OneCore\Voices\Tokens"),
            ]
            seen = set()
            for hive, path in registry_paths:
                try:
                    with winreg.OpenKey(hive, path) as key:
                        for n in range(winreg.QueryInfoKey(key)[0]):
                            token = winreg.EnumKey(key, n)
                            with winreg.OpenKey(key, token) as token_key:
                                try:
                                    name = winreg.QueryValueEx(token_key, "")[0]
                                except OSError:
                                    name = token
                                name = str(name).strip()
                                if name and name.lower() not in seen:
                                    seen.add(name.lower())
                                    voices.append((name, name))
                except OSError:
                    continue
            if voices:
                return voices
        except Exception as e:
            print("SAPI registry enumeration error:", e)

        command = (
            "$v = New-Object -ComObject SAPI.SpVoice; "
            "$a = @($v.GetVoices() | ForEach-Object { $_.GetDescription() }); "
            "$a | ConvertTo-Json -Compress"
        )
        try:
            result = subprocess.run(
                [self._powershell_exe(), "-NoProfile", "-NonInteractive", "-Command", command],
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=8,
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
            )
            raw = result.stdout.strip()
            if not raw:
                return []
            values = json.loads(raw)
            if isinstance(values, str):
                values = [values]
            return [(name, name) for name in values if isinstance(name, str) and name.strip()]
        except Exception as e:
            print("SAPI voice enumeration error:", e)
            return []

    def _powershell_exe(self):
        """Resolve Windows PowerShell reliably from a frozen or normal app."""
        if sys.platform != "win32":
            return "powershell"
        system_root = os.environ.get("SystemRoot", r"C:\Windows")
        candidates = []
        # Sysnative lets a 32-bit frozen app reach the native 64-bit PowerShell.
        if os.environ.get("PROCESSOR_ARCHITEW6432"):
            candidates.append(os.path.join(system_root, "Sysnative", "WindowsPowerShell", "v1.0", "powershell.exe"))
        candidates.append(os.path.join(system_root, "System32", "WindowsPowerShell", "v1.0", "powershell.exe"))
        for path in candidates:
            if os.path.exists(path):
                return path
        return "powershell.exe"

    def _tts_worker(self):
        while not self._tts_stop.is_set():
            try:
                text = self._speak_queue.get(timeout=0.3)
            except queue.Empty:
                continue
            if text is None:
                break
            self._speaking = True
            try:
                self._speak_via_powershell(text)
            except Exception as e:
                print("TTS error:", e)
            finally:
                self._speaking = False
                try:
                    self._speak_queue.task_done()
                except:
                    pass

    def _speak_via_powershell(self, text):
        """Windows built-in, no pip needed. Runs in worker thread so UI never freezes."""
        if sys.platform != "win32":
            # macOS / Linux fallback
            try:
                if sys.platform == "darwin":
                    subprocess.run(["say", text], timeout=30)
                else:
                    subprocess.run(["espeak", text], timeout=30)
            except Exception as e:
                print("Fallback TTS error:", e)
            return
        # Map 125/175/225 wpm -> SAPI Rate -5 / 0 / +5.
        sapi_rate = max(-10, min(10, int((self.narration_rate - 175) / 10)))
        voice = ""
        if self.narration_voices:
            idx = max(0, min(self.narration_voice_idx, len(self.narration_voices) - 1))
            voice = self.narration_voices[idx][0]
        # Base64 avoids quoting bugs for Bible text, apostrophes, and voice names.
        text_b64 = base64.b64encode(text.encode("utf-8")).decode("ascii")
        voice_b64 = base64.b64encode(voice.encode("utf-8")).decode("ascii")
        cmd = [
            self._powershell_exe(), "-NoProfile", "-NonInteractive", "-Command",
            "$s = New-Object -ComObject SAPI.SpVoice; "
            f"$text = [Text.Encoding]::UTF8.GetString([Convert]::FromBase64String('{text_b64}')); "
            f"$voice = [Text.Encoding]::UTF8.GetString([Convert]::FromBase64String('{voice_b64}')); "
            f"$s.Rate = {sapi_rate}; "
            "if ($voice) { $token = $s.GetVoices() | Where-Object { $_.GetDescription() -eq $voice } | Select-Object -First 1; if ($token) { $s.Voice = $token } }; "
            "$s.Speak($text); [void][Runtime.InteropServices.Marshal]::ReleaseComObject($s)"
        ]
        try:
            self._tts_process = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, close_fds=True, creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            self._tts_process.wait()
        except Exception as e:
            print("PowerShell TTS error:", e)
        finally:
            self._tts_process = None

    def _clean_text_for_speech(self, text):
        """Make verse text sound natural when spoken."""
        t = text.strip()
        # Remove common verse formatting that sounds odd spoken
        t = re.sub(r"[\u201c\u201d]", '"', t)
        t = re.sub(r"[\u2018\u2019]", "'", t)
        # "John 3:16 - For God..." -> "John 3, verse 16. For God..."
        # Keep it light: just replace dash separators with a pause
        t = t.replace(" — ", ", ").replace(" -- ", ", ").replace(" - ", ", ")
        t = re.sub(r"\s+", " ", t)
        # Strip emojis / symbols that TTS would spell out
        t = re.sub(r"[^\w\s\.,;:!?\'\"\-\(\)]", "", t)
        return t.strip()

    def speak_current(self, force=False):
        if not self.lines:
            return
        if not force and not self.narration_enabled:
            return
        self.stop_narration()
        text = self._clean_text_for_speech(self.lines[self.index].strip())
        if not text:
            return
        # Clear any stale queued items, then queue this one
        try:
            while True:
                self._speak_queue.get_nowait()
        except queue.Empty:
            pass
        self._speak_queue.put(text)
        t = self.themes[self.current_theme]
        self.info.config(text="🔊 Speaking...", fg=t["glow"])
        # Restore info label after a bit (speech continues in background)
        self.root.after(1500, lambda: self.info.config(text=os.path.basename(self.filepath) if self.filepath else "", fg=t["info_fg"]))

    def stop_narration(self):
        try:
            while True:
                self._speak_queue.get_nowait()
        except queue.Empty:
            pass
        if self._tts_process is not None:
            try:
                self._tts_process.terminate()
            except:
                pass
            self._tts_process = None

    def _shutdown_tts(self):
        self._tts_stop.set()
        self.stop_narration()
        try:
            self._speak_queue.put(None)
        except:
            pass

    def toggle_narration(self):
        self.narration_enabled = not self.narration_enabled
        try:
            self.narration_var.set(self.narration_enabled)
        except:
            pass
        if not self.narration_enabled:
            self.narration_auto = False
            try:
                self.narration_auto_var.set(False)
            except:
                pass
            self.stop_narration()
        self.update_narration_visual()
        self.save_config()
        if self.narration_enabled:
            # Speak current verse immediately so user hears it working
            self.speak_current()

    def toggle_auto_narrate(self):
        self.narration_auto = not self.narration_auto
        if self.narration_auto and not self.narration_enabled:
            self.narration_enabled = True
        try:
            self.narration_auto_var.set(self.narration_auto)
            self.narration_var.set(self.narration_enabled)
        except:
            pass
        if not self.narration_auto:
            self.stop_narration()
        self.update_narration_visual()
        self.save_config()
        if self.narration_auto:
            self.speak_current()

    def set_narration_rate(self, rate):
        self.narration_rate = rate
        t = self.themes[self.current_theme]
        label = {125: "Slow", 175: "Normal", 225: "Fast"}.get(rate, f"{rate} wpm")
        self.info.config(text=f"Narration: {label}", fg=t["glow"])
        self.root.after(800, lambda: self.info.config(text=os.path.basename(self.filepath) if self.filepath else "", fg=t["info_fg"]))
        self.save_config()

    def _apply_narration_voice(self):
        if not self.narration_voices:
            return
        try:
            idx = max(0, min(self.narration_voice_idx, len(self.narration_voices)-1))
            self.narration_voice_idx = idx
        except:
            pass

    def set_narration_voice(self, idx):
        self.narration_voice_idx = idx
        self._apply_narration_voice()
        self.save_config()
        # Preview with a short phrase
        if self.narration_enabled:
            self.stop_narration()
            self._speak_queue.put("Narration voice selected.")

    def _rebuild_voice_menu(self):
        try:
            self.voice_menu.delete(0, "end")
        except:
            return
        if not self.narration_voices:
            label = "No Windows SAPI voices found" if sys.platform == "win32" else "Windows SAPI voices are unavailable"
            self.voice_menu.add_command(label=label, command=lambda: None)
            return
        for i, (vid, name) in enumerate(self.narration_voices):
            display = name[:48]
            prefix = "✓ " if i == self.narration_voice_idx else ""
            self.voice_menu.add_command(label=prefix + display, command=lambda idx=i: self.set_narration_voice(idx))

    def update_narration_visual(self):
        t = self.themes[self.current_theme]
        if self.narration_enabled:
            # 🔊 if on, with auto indicator in tooltip-style via info on hover
            self.narration_btn.config(text="🔊", fg="#22c55e" if not self.narration_auto else "#7dd3fc")
        else:
            self.narration_btn.config(text="🔇", fg=t["info_fg"])

    def on_narration_enter(self, e):
        if self.narration_enabled:
            tip = "Auto-narrate: ON - click to turn off" if self.narration_auto else "Narration: ON - click to turn off"
        else:
            tip = "Narration: OFF - click to turn on"
        self.info.config(text=tip, fg=self.themes[self.current_theme]["glow"])

    def on_narration_leave(self, e):
        t = self.themes[self.current_theme]
        self.info.config(text=os.path.basename(self.filepath) if self.filepath else "", fg=t["info_fg"])
        self.update_narration_visual()

    def save_config(self, force=False):
        """Debounced save (v6.1 fix).

        Old code did open(settings.dat, 'w') on EVERY verse change. If the file
        was momentarily locked (PowerShell TTS child, a 2nd VerseBox instance,
        OneDrive/Defender scanning AppData) Windows raised Errno 13 and then
        spammed the error forever. Now we coalesce rapid saves, write to a
        temp file then os.replace() (atomic), retry 3x, then stay quiet 10s.
        """
        try:
            if threading.current_thread() is not threading.main_thread():
                self.root.after(0, lambda: self.save_config(force=force))
                return
        except:
            pass
        if force:
            self._do_save()
            return
        try:
            if self._save_job is not None:
                self.root.after_cancel(self._save_job)
        except:
            pass
        try:
            self._save_job = self.root.after(300, self._do_save)
        except:
            self._do_save()

    def _do_save(self):
        self._save_job = None
        try:
            data = {"file":self.filepath,"idx":self.index,"font":self.font_size,"geom":self.root.geometry(),
                    "opacity":self.opacity,"auto":self.auto_enabled,"delay":self.auto_delay,
                    "top":self.top_var.get(),"shuffle":self.shuffle_enabled,"theme":self.current_theme,
                    "pinned":self.is_pinned,
                    "narration":self.narration_enabled,"narration_auto":self.narration_auto,
                    "narration_rate":self.narration_rate,"narration_voice":self.narration_voice_idx,
                    "history":self.view_history[-50:],"history_position":self.history_position}
            payload = _encode_config(data)
            tmp_path = f"{CONFIG_FILE}.tmp.{os.getpid()}"
            last_err = None
            for attempt, delay in enumerate([0, 0.1, 0.3, 0.6]):
                try:
                    if delay:
                        self._time_mod.sleep(delay)
                    with open(tmp_path, "w", encoding="utf-8") as f:
                        f.write(payload)
                        f.flush()
                        try:
                            os.fsync(f.fileno())
                        except:
                            pass
                    os.replace(tmp_path, CONFIG_FILE)
                    _set_hidden(CONFIG_FILE)
                    return
                except (PermissionError, OSError) as e:
                    last_err = e
                    try:
                        if os.path.exists(tmp_path):
                            os.remove(tmp_path)
                    except:
                        pass
                    continue
            now = self._time_mod.time()
            if now - self._last_save_error_at > 10:
                self._last_save_error_at = now
                print(f"save config skipped (file locked, will retry on next change): {last_err}")
        except Exception as e:
            now = self._time_mod.time()
            if now - self._last_save_error_at > 10:
                self._last_save_error_at = now
                print("save config error", e)
        
    def load_config(self):
        try:
            if not os.path.exists(CONFIG_FILE):
                migrated = _migrate_old_config()
                if migrated:
                    d = migrated
                else:
                    d = {}
            else:
                with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                    d = _decode_config(f.read())
            
            if d:
                self.font_size=max(14, min(56, d.get("font",40)))
                self.view_history=d.get("history", [])[-50:]
                self.history_position=min(d.get("history_position", len(self.view_history)-1), len(self.view_history)-1)
                self.opacity=d.get("opacity",0.96); self.root.attributes("-alpha",self.opacity)
                self.root.geometry(d.get("geom","600x170+120+120"))
                self.top_var.set(d.get("top",True)); self.root.attributes("-topmost",self.top_var.get())
                self.auto_enabled=d.get("auto",False); self.auto_var.set(self.auto_enabled)
                self.auto_delay=d.get("delay",6000)
                self.shuffle_enabled=d.get("shuffle",False); self.shuffle_var.set(self.shuffle_enabled)
                self.is_pinned=d.get("pinned",False); self.pin_var.set(self.is_pinned)
                self.narration_enabled=d.get("narration",False)
                self.narration_auto=d.get("narration_auto",False)
                self.narration_rate=d.get("narration_rate",175)
                self.narration_voice_idx=d.get("narration_voice",0)
                try:
                    self.narration_var.set(self.narration_enabled)
                    self.narration_auto_var.set(self.narration_auto)
                    self._apply_narration_voice()
                    self.update_narration_visual()
                except:
                    pass
                self.current_theme = d.get("theme","Original Dark")
                self.theme_var.set(self.current_theme)
                fp=d.get("file")
                if fp and os.path.exists(fp):
                    with open(fp,encoding="utf-8",errors="replace") as f: self.lines=[l.rstrip() for l in f if l.strip()]
                    self.filepath=fp; self.index=min(d.get("idx",0),len(self.lines)-1)
                    self.info.config(text=os.path.basename(fp) + (" [SHUFFLE]" if self.shuffle_enabled else ""))
                    if not self.view_history:
                        self.view_history.append({"file": fp, "index": self.index, "text": self.lines[self.index].strip()})
                        self.history_position = 0
                # apply pin visual after load
                try:
                    self.root.after(100, self.update_pin_visual)
                except:
                    pass
        except Exception as e:
            print("load config error", e)
            self.center_window()

if __name__=="__main__":
    root=tk.Tk()
    app=BorderlessViewerV5(root)
    root.mainloop()
