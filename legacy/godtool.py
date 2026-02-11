"""
Mario Kart Wii Save Editor godtool
sponsored by ChatGPT o4-mini-high

Features:
- Per-license sub-tabs: DWC Data, Friends, Unlocks, Records, Cups, Leaderboards, Character, Vehicle, Course, Stage
- Big-endian DWC field access & CRC-32
- Global save-file CRC-32 recompute (big-endian)
- License import/export (.rkp), copy, delete, blank
- Records editing: full set of statistics
- Cups editing: trophy type, star rank, completion flag, and presets per cup
- Unlocks editing: cup completions, character unlocks, vehicle unlocks with "Unlock All"
- Favorite Character/Vehicle/Course/Stage counts per license
- Friends import/export to CSV with full main-block data
- Tools to complete all staff ghost flags (normal/expert), change region
"""
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, filedialog, messagebox, simpledialog
import csv
import struct, zlib, hashlib

# Constants
LICENSE_OFFSETS = [0x08, 0x8CC8, 0x11988, 0x1A648]
LICENSE_SIZE    = 0x8CC0
DWC_OFFSET      = 0x40
DWC_DATA_LEN    = 0x3C
FRIEND_MAIN_OFFSET = 0x56D0
FRIEND_STRIDE   = 0x1C0
NUM_FRIENDS     = 30
GLOBAL_CRC_OFFSET = 0x27FFC
REGION_ID_OFFSET       = 0x26B0A  # UInt16 Region ID in RKGD
REGION_IDS = {
    "Japan": 0x0000,
    "Americas": 0x1000,
    "Europe": 0x2000,
    "Australia/New Zealand": 0x3000,
    "Taiwan": 0x4000,
    "South Korea": 0x5000,
    "China": 0x6000
}

# DWC fields relative to DWC_OFFSET
DWC_FIELDS = [
    ("Pseudo User ID #1", 0x04),
    ("Pseudo User ID #2", 0x08),
    ("Pseudo Player ID",    0x0C),
    ("Authentic User ID #1", 0x10),
    ("Authentic User ID #2", 0x14),
    ("Authentic Player ID",  0x18),
    ("Player Profile ID",    0x1C)
]

FRIEND_FIELDS = [
    ("Unknown1",      0x00, 'i'),
    ("ProfileID",     0x04, 'I'),
    ("Unknown2",      0x08, 'i'),
    ("UnknownBytes1", 0x0C, '4s'),
    ("Flag",          0x10, 'H'),
    ("Losses",        0x12, 'H'),
    ("Wins",          0x14, 'H'),
    ("RaceRating",    0x16, 'H'),
    ("BattleRating",  0x18, 'H'),
    ("MiiData",       0x1A, '74s'),  # 0x4A bytes
    ("UnknownBytes2", 0x64, '4s'),
    ("CountryID",     0x68, 'B'),
    ("RegionID",      0x69, 'B'),
    ("Unknown3",      0x6A, 'H'),
    ("GlobeX",        0x6C, 'H'),
    ("GlobeY",        0x6E, 'H'),
    ("Unknown4",      0x70, '336s') # remainder: 0x150 bytes
]

# Records Offsets relative to license base
RECORD_OFFSETS = [
    ("Offline Wins (Race)",       0x88, 'i'),
    ("Offline Losses (Race)",     0x8C, 'i'),
    ("Offline Wins (Battle)",     0x90, 'i'),
    ("Offline Losses (Battle)",   0x94, 'i'),
    ("WFC Wins (Race)",           0x98, 'i'),
    ("WFC Losses (Race)",         0x9C, 'i'),
    ("WFC Wins (Battle)",         0xA0, 'i'),
    ("WFC Losses (Battle)",       0xA4, 'i'),
    ("Ghost Race Wins",           0xA8, 'i'),
    ("Ghost Race Losses",         0xAC, 'i'),
    ("Race Rating",               0xB0, 'H'),
    ("Battle Rating",             0xB2, 'H'),
    ("Total Race Count",          0xB4, 'i'),
    ("Total Battle Count",        0xB8, 'i'),
    ("Wii Wheel Races",           0xBC, 'i'),
    ("Wii Wheel Battles",         0xC0, 'i'),
    ("Distance Travelled",        0xC4, 'f'),
    ("Ghost Challenges Sent",     0xC8, 'i'),
    ("Ghost Challenges Received", 0xCC, 'i'),
    ("Item Hits Delivered",       0xD0, 'i'),
    ("Item Hits Received",        0xD4, 'i'),
    ("Tricks Performed",          0xD8, 'i'),
    ("Times 1st Place",           0xDC, 'i'),
    ("Distance 1st Place",        0xE0, 'f'),
    ("Distance VS Races",         0xE4, 'f'),
    ("Competitions Entered",      0xE8, 'H'),
]

# Cups Offsets relative to license base
CUP_OFFSETS = [
    ("Mushroom Cup (50cc)",   0x1C0),
    ("Flower Cup (50cc)",     0x220),
    ("Star Cup (50cc)",       0x280),
    ("Special Cup (50cc)",    0x2E0),
    ("Shell Cup (50cc)",      0x340),
    ("Banana Cup (50cc)",     0x3A0),
    ("Leaf Cup (50cc)",       0x400),
    ("Lightning Cup (50cc)",  0x460),
    ("Mushroom Cup (100cc)",  0x4C0),
    ("Flower Cup (100cc)",    0x520),
    ("Star Cup (100cc)",      0x580),
    ("Special Cup (100cc)",   0x5E0),
    ("Shell Cup (100cc)",     0x640),
    ("Banana Cup (100cc)",    0x6A0),
    ("Leaf Cup (100cc)",      0x700),
    ("Lightning Cup (100cc)", 0x760),
    ("Mushroom Cup (150cc)",  0x7C0),
    ("Flower Cup (150cc)",    0x820),
    ("Star Cup (150cc)",      0x880),
    ("Special Cup (150cc)",   0x8E0),
    ("Shell Cup (150cc)",     0x940),
    ("Banana Cup (150cc)",    0x9A0),
    ("Leaf Cup (150cc)",      0xA00),
    ("Lightning Cup (150cc)", 0xA60),
    ("Mushroom Cup (Mirror)", 0xAC0),
    ("Flower Cup (Mirror)",   0xB20),
    ("Star Cup (Mirror)",     0xB80),
    ("Special Cup (Mirror)",  0xBE0),
    ("Shell Cup (Mirror)",    0xC40),
    ("Banana Cup (Mirror)",   0xCA0),
    ("Leaf Cup (Mirror)",     0xD00),
    ("Lightning Cup (Mirror)",0xD60),
]

# Trophy types and rank labels
TROPHY_TYPES = ["Gold","Silver","Bronze","None"]
STAR_RANKS    = ["3 Stars","2 Stars","1 Star","A","B","C","D","E","F"]

# Levels of unlock bits by offset and bit
UNLOCK_FLAGS = [
    # Cup completion bits
    ("Karts 100cc", 0x30, 0),
    ("Bikes 50cc",  0x30, 1),
    ("Leaf Cup Mirror",    0x30, 2),
    ("Leaf Cup 150cc",     0x30, 3),
    ("Leaf Cup 100cc",     0x30, 4),
    ("Leaf Cup 50cc",      0x30, 5),
    ("Banana Cup Mirror",  0x30, 6),
    ("Banana Cup 150cc",   0x30, 7),
    ("Banana Cup 100cc",   0x31, 0),
    ("Banana Cup 50cc",    0x31, 1),
    ("Star Cup Mirror",    0x31, 2),
    ("Star Cup 150cc",     0x31, 3),
    ("Star Cup 100cc",     0x31, 4),
    ("Star Cup 50cc",      0x31, 5),
    ("Flower Cup Mirror",  0x31, 6),
    ("Flower Cup 150cc",   0x31, 7),
    ("Flower Cup 100cc",   0x32, 0),
    ("Flower Cup 50cc",    0x32, 1),
    # Character unlocks
    ("Mii Outfit B",       0x32, 2),
    ("Mii Outfit A",       0x32, 3),
    ("Rosalina",           0x32, 4),
    ("Funky Kong",         0x32, 5),
    ("King Boo",           0x32, 6),
    ("Dry Bowser",         0x32, 7),
    ("Birdo",              0x33, 0),
    ("Daisy",              0x33, 1),
    ("Bowser Jr.",         0x33, 2),
    ("Diddy Kong",         0x33, 3),
    ("Baby Luigi",         0x33, 4),
    ("Baby Daisy",         0x33, 5),
    ("Toadette",           0x33, 6),
    ("Dry Bones",          0x33, 7),
    # Vehicle unlocks
    ("Phantom",            0x35, 4),
    ("Spear",              0x35, 5),
    ("Shooting Star",      0x35, 6),
    ("Dolphin Dasher",     0x35, 7),
    ("Sneakster",          0x36, 0),
    ("Zip Zip",            0x36, 1),
    ("Jet Bubble",         0x36, 2),
    ("Magikruiser",        0x36, 3),
    ("Quacker",            0x36, 4),
    ("Honeycoupe",         0x36, 5),
    ("Jetsetter",          0x36, 6),
    ("Piranha Prowler",    0x36, 7),
    ("Sprinter",           0x37, 0),
    ("Daytripper",         0x37, 1),
    ("Super Blooper",      0x37, 2),
    ("Blue Falcon",        0x37, 3),
    ("Tiny Titan",         0x37, 4),
    ("Cheep Charger",      0x37, 5)
]

FAVORITE_CHARACTERS = [
    ("Mario",       0xEC), ("Baby Peach", 0xEE), ("Waluigi",    0xF0),
    ("Bowser",     0xF2), ("Baby Daisy", 0xF4), ("Dry Bones",  0xF6),
    ("Baby Mario", 0xF8), ("Luigi",       0xFA), ("Toad",       0xFC),
    ("Donkey Kong",0xFE), ("Yoshi",       0x100),("Wario",      0x102),
    ("Baby Luigi",0x104), ("Toadette",    0x106),("Koopa Troopa",0x108),
    ("Daisy",      0x10A),("Peach",      0x10C),("Birdo",      0x10E),
    ("Diddy Kong",0x110),("King Boo",   0x112),("Bowser Jr.",0x114),
    ("Dry Bowser",0x116),("Funky Kong", 0x118),("Rosalina",   0x11A),
    ("Mii",        0x11C)
]

FAVORITE_VEHICLES = [
    ("Standard Kart S",0x11E),("Standard Kart M",0x120),("Standard Kart L",0x122),
    ("Booster Seat",0x124),("Classic Dragster",0x126),("Offroader",0x128),
    ("Mini Beast",0x12A),("Wild Wing",0x12C),("Flame Flyer",0x12E),
    ("Cheep Charger",0x130),("Super Blooper",0x132),("Piranha Prowler",0x134),
    ("Tiny Titan",0x136),("Daytripper",0x138),("Jetsetter",0x13A),
    ("Blue Falcon",0x13C),("Sprinter",0x13E),("Honeycoupe",0x140),
    ("Standard Bike S",0x142),("Standard Bike M",0x144),("Standard Bike L",0x146),
    ("Bullet Bike",0x148),("Mach Bike",0x14A),("Flame Runner",0x14C),
    ("Bit Bike",0x14E),("Sugarscoot",0x150),("Wario Bike",0x152),
    ("Quacker",0x154),("Zip Zip",0x156),("Shooting Star",0x158),
    ("Magikruiser",0x15A),("Sneakster",0x15C),("Spear",0x15E),
    ("Jet Bubble",0x160),("Dolphin Dasher",0x162),("Phantom",0x164)
]

FAVORITE_COURSES = [
    ("Mario Circuit",0x166),("Moo Moo Meadows",0x168),("Mushroom Gorge",0x16A),
    ("Grumble Volcano",0x16C),("Toad's Factory",0x16E),("Coconut Mall",0x170),
    ("DK Summit",0x172),("Wario's Gold Mine",0x174),("Luigi Circuit",0x176),
    ("Daisy Circuit",0x178),("Moonview Highway",0x17A),("Maple Treeway",0x17C),
    ("Bowser's Castle",0x17E),("Rainbow Road",0x180),("Dry Dry Ruins",0x182),
    ("Koopa Cape",0x184),("GCN Peach Beach",0x186),("GCN Mario Circuit",0x188),
    ("GCN Waluigi Stadium",0x18A),("GCN DK Mountain",0x18C),("DS Yoshi Falls",0x18E),
    ("DS Desert Hills",0x190),("DS Peach Gardens",0x192),("DS Delfino Square",0x194),
    ("SNES Mario Circuit 3",0x196),("SNES Ghost Valley 2",0x198),
    ("N64 Mario Raceway",0x19A),("N64 Sherbet Land",0x19C),("N64 Bowser's Castle",0x19E),
    ("N64 DK's Jungle Parkway",0x1A0),("GBA Bowser Castle 3",0x1A2),("GBA Shy Guy Beach",0x1A4)
]

FAVORITE_STAGES = [
    ("Delfino Pier",0x1A6),("Block Plaza",0x1A8),("Chain Chomp Wheel",0x1AA),
    ("Funky Stadium",0x1AC),("Thwomp Desert",0x1AE),("GCN Cookie Land",0x1B0),
    ("DS Twilight House",0x1B2),("SNES Battle Course 4",0x1B4),("GBA Battle Course 3",0x1B6),
    ("N64 Skyscraper",0x1B8)
]

# Utility functions

def reverse_crc32(data: bytes) -> int:
    rev = bytearray()
    for i in range(0, len(data), 4): rev.extend(data[i:i+4][::-1])
    return zlib.crc32(rev) & 0xFFFFFFFF


def compute_global_crc(content: bytearray) -> int:
    return zlib.crc32(content[:GLOBAL_CRC_OFFSET]) & 0xFFFFFFFF


def pid_to_friend_code(pid: int) -> str:
    buf = pid.to_bytes(4, 'little') + b'JCMR'
    md5 = hashlib.md5(buf).digest()
    csum = md5[0] >> 1
    fc64 = (csum << 32) | pid
    s = f"{fc64:012d}"
    return f"{s[:4]}-{s[4:8]}-{s[8:]}"

class SaveEditorApp:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Godtool by Gab")
        self.content = bytearray()
        self.filepath = None
        self.dwc_vars    = {}
        self.fc_vars     = {}
        self.friend_views= {}
        self.record_vars = {}
        self.fav_vars = {}
        self.cup_vars    = {}  # (lic, offset) -> (t_var, r_var)
        self.unlock_vars = {}  # (lic,offset,bit): IntVar
        self._build_menu()
        self.notebook = ttk.Notebook(self.root)
        for lic in range(4):
            tab = self._create_license_tab(lic)
            self.notebook.add(tab, text=f"License {lic+1}")
        self.notebook.pack(fill='both', expand=True)
        self.root.mainloop()

    def _build_menu(self):
        m = tk.Menu(self.root)
        fm = tk.Menu(m, tearoff=0)
        fm.add_command(label="Open...", command=self.open_file)
        fm.add_command(label="Save",   command=self.save_file)
        fm.add_command(label="Save As...", command=self.save_file_as)
        fm.add_separator(); fm.add_command(label="Exit", command=self.root.quit)
        m.add_cascade(label="File", menu=fm)
        lm = tk.Menu(m, tearoff=0)
        lm.add_command(label="Export License...", command=self.export_license)
        lm.add_command(label="Import License...", command=self.import_license)
        lm.add_command(label="Copy License...",   command=self.copy_license)
        lm.add_separator()
        lm.add_command(label="Delete License",    command=self.delete_license)
        lm.add_command(label="Blank License",     command=self.blank_license)
        m.add_cascade(label="License", menu=lm)
        tm = tk.Menu(m, tearoff=0)
        tm.add_command(label="Recompute CRCs", command=self.recompute_crcs)
        tm.add_command(label="Show Global CRC", command=self.show_global_crc)
        tm.add_separator()
        tm.add_command(label="Change Region...", command=self._change_region)
        tm.add_separator()
        tm.add_command(label="Complete Normal Staff Ghosts", command=self._complete_normal_staff)
        tm.add_command(label="Complete Expert Staff Ghosts", command=self._complete_expert_staff)
        tm.add_separator()
        tm.add_command(label="Export Friends...", command=self._export_friends)
        tm.add_command(label="Import Friends...", command=self._import_friends)
        m.add_cascade(label="Tools", menu=tm)
        self.root.config(menu=m)

    def _create_license_tab(self, lic):
        f = ttk.Frame(self.notebook)
        sub = ttk.Notebook(f)
        # DWC Data
        dwcf = ttk.Frame(sub, padding=5)
        self._build_dwc_editor(dwcf, lic)
        sub.add(dwcf, text="DWC Data")
        # Friends
        fv = self._build_friend_viewer(lic)
        sub.add(fv, text="Friends")
        # Records
        rv = self._build_records_viewer(lic)
        sub.add(rv, text="Records")
        # Cups
        cv = self._build_cups_viewer(lic)
        sub.add(cv, text="Cups")
        # Unlocks
        uv = self._build_unlocks_viewer(lic)
        sub.add(uv, text="Unlocks")
        char_tab = self._build_favorite_viewer(lic, FAVORITE_CHARACTERS, "Characters")
        sub.add(char_tab, text="Characters")
        veh_tab = self._build_favorite_viewer(lic, FAVORITE_VEHICLES, "Vehicles")
        sub.add(veh_tab, text="Vehicles")
        course_tab = self._build_favorite_viewer(lic, FAVORITE_COURSES, "Courses")
        sub.add(course_tab, text="Courses")
        stage_tab = self._build_favorite_viewer(lic, FAVORITE_STAGES, "Stages")
        sub.add(stage_tab, text="Stages")
        # Leaderboards stub
        lb = ttk.Frame(sub, padding=20)
        ttk.Label(lb, text="More coming soonTM...").pack()
        sub.add(lb, text="Empty")
        sub.pack(fill='both', expand=True)
        return f

    def _build_dwc_editor(self, parent, lic):
        for i,(lbl,off) in enumerate(DWC_FIELDS):
            ttk.Label(parent, text=lbl).grid(row=i, column=0, sticky='e')
            v = tk.StringVar()
            ttk.Entry(parent, textvariable=v, width=16).grid(row=i, column=1, padx=5)
            self.dwc_vars[(lic,off)] = v
            if off==0x1C:
                fc = tk.StringVar(); self.fc_vars[lic] = fc
                ttk.Label(parent, textvariable=fc).grid(row=i, column=2)
        btn = ttk.Button(parent, text="Apply & CRC", command=lambda l=lic: self._apply_dwc(l))
        btn.grid(row=len(DWC_FIELDS), column=0, columnspan=3, pady=5)

    def _build_friend_viewer(self, lic):
        f = ttk.Frame(self.notebook)
        cols=("Slot","PID","Code","Wins","Losses","RaceR","BattleR")
        tv = ttk.Treeview(f, columns=cols, show='headings')
        for c in cols: tv.heading(c, text=c); tv.column(c, width=80)
        tv.pack(fill='both', expand=True); self.friend_views[lic] = tv
        return f

    def _build_records_viewer(self, lic):
        f = ttk.Frame(self.notebook, padding=5)
        # you’ll need at top of file: import tkinter.font as tkfont
        bold_font = tkfont.Font(weight='bold')

        # --- Top row: Race & Battle Rating ---
        # Race Rating
        rr_label, rr_off, rr_typ = RECORD_OFFSETS[10]   # index 10
        ttk.Label(f, text=rr_label, font=bold_font) \
            .grid(row=0, column=0, sticky='e', padx=5, pady=2)
        rr_var = tk.StringVar()
        ttk.Entry(f, textvariable=rr_var, width=12) \
            .grid(row=0, column=1, padx=5, pady=2)
        self.record_vars[(lic, rr_off)] = (rr_var, rr_typ)

        # Battle Rating
        br_label, br_off, br_typ = RECORD_OFFSETS[11]   # index 11
        ttk.Label(f, text=br_label, font=bold_font) \
            .grid(row=0, column=2, sticky='e', padx=5, pady=2)
        br_var = tk.StringVar()
        ttk.Entry(f, textvariable=br_var, width=12) \
            .grid(row=0, column=3, padx=5, pady=2)
        self.record_vars[(lic, br_off)] = (br_var, br_typ)

        # --- Other stats starting at row 1 ---
        row = 1
        col = 0
        for label, off, typ in RECORD_OFFSETS:
            if off in (rr_off, br_off):
                continue
            ttk.Label(f, text=label) \
                .grid(row=row, column=col, sticky='e', padx=5, pady=2)
            v = tk.StringVar()
            ttk.Entry(f, textvariable=v, width=12) \
                .grid(row=row, column=col+1, padx=5, pady=2)
            self.record_vars[(lic, off)] = (v, typ)

            col += 2
            if col >= 4:
                col = 0
                row += 1

        # Apply button below
        btn = ttk.Button(f, text="Apply Records",
                         command=lambda l=lic: self._apply_records(l))
        btn.grid(row=row+1, column=0, columnspan=4, pady=10)

        return f


    def _build_cups_viewer(self, lic):
        f = ttk.Frame(self.notebook, padding=5)
        # Layout cups in two columns: label, trophy, rank, done
        for idx, (lbl, off) in enumerate(CUP_OFFSETS):
            row = idx // 2
            col = (idx % 2) * 4
            ttk.Label(f, text=lbl).grid(row=row, column=col, sticky='e', padx=5, pady=2)
            # Trophy type
            tvar = tk.StringVar()
            cb_t = ttk.Combobox(f, values=TROPHY_TYPES, textvariable=tvar, state='readonly', width=8)
            cb_t.grid(row=row, column=col+1, padx=2, pady=2)
            # Star rank
            rvar = tk.StringVar()
            cb_r = ttk.Combobox(f, values=STAR_RANKS, textvariable=rvar, state='readonly', width=8)
            cb_r.grid(row=row, column=col+2, padx=2, pady=2)
            # Completion flag
            cvar = tk.IntVar()
            cb_c = tk.Checkbutton(f, text="Done", variable=cvar)
            cb_c.grid(row=row, column=col+3, padx=2, pady=2)
            self.cup_vars[(lic, off)] = (tvar, rvar, cvar)
        total_rows = (len(CUP_OFFSETS) + 1) // 2
        # Preset buttons for star ranks and clear
        preset_frame = ttk.Frame(f)
        preset_frame.grid(row=total_rows, column=0, columnspan=8, pady=5)
        ttk.Button(preset_frame, text="All 3 Stars",
                   command=lambda l=lic: self._preset_cup_ranks(l, 0)).pack(side='left', padx=2)
        ttk.Button(preset_frame, text="All 2 Stars",
                   command=lambda l=lic: self._preset_cup_ranks(l, 1)).pack(side='left', padx=2)
        ttk.Button(preset_frame, text="All 1 Star",
                   command=lambda l=lic: self._preset_cup_ranks(l, 2)).pack(side='left', padx=2)
        ttk.Button(preset_frame, text="Clear All",
                   command=lambda l=lic: self._clear_all_cups(l)).pack(side='left', padx=2)
        # Apply button
        btn = ttk.Button(f, text="Apply Cups", command=lambda l=lic: self._apply_cups(l))
        btn.grid(row=total_rows+1, column=0, columnspan=8, pady=10)
        return f

    def open_file(self):
        fn = filedialog.askopenfilename(filetypes=[("DAT","*.dat")])
        if not fn: return
        self.content = bytearray(open(fn,'rb').read()); self.filepath = fn; self._refresh_all()

    def save_file(self):
        if not self.filepath: return self.save_file_as()
        self._write_global_crc(); open(self.filepath,'wb').write(self.content)
        messagebox.showinfo("Saved","File saved.")

    def save_file_as(self):
        fn = filedialog.asksaveasfilename(defaultextension='.dat',filetypes=[("DAT","*.dat")])
        if not fn: return
        self.filepath = fn; self.save_file()

    def _select_license(self,prompt):
        v = simpledialog.askinteger("License", prompt+" (1-4)", minvalue=1, maxvalue=4)
        return None if v is None else v-1

    def export_license(self):
        idx = self._select_license("Export license #")
        if idx is None:
            return
        fn = filedialog.asksaveasfilename(defaultextension='.rkp')
        if not fn:
            return
        base = LICENSE_OFFSETS[idx]
        open(fn, 'wb').write(self.content[base:base+LICENSE_SIZE])
        messagebox.showinfo("Exported", f"License {idx+1} exported.")

    def import_license(self):
        idx = self._select_license("Import license #")
        if idx is None:
            return
        fn = filedialog.askopenfilename(filetypes=[("RKP","*.rkp")])
        data = open(fn, 'rb').read()
        if len(data) != LICENSE_SIZE:
            messagebox.showerror("Error", "Invalid .rkp size")
            return
        base = LICENSE_OFFSETS[idx]
        self.content[base:base+LICENSE_SIZE] = data
        self._refresh_all()
        messagebox.showinfo("Imported", f"License {idx+1} imported.")

    def copy_license(self):
        src = self._select_license("Copy from #")
        dst = self._select_license("Paste to #")
        if src is None or dst is None:
            return
        a = LICENSE_OFFSETS[src]
        b = LICENSE_OFFSETS[dst]
        self.content[b:b+LICENSE_SIZE] = self.content[a:a+LICENSE_SIZE]
        self._refresh_all()
        messagebox.showinfo("Copied", f"{src+1}->{dst+1}")

    def delete_license(self):
        idx = self._select_license("Delete license #")
        if idx is None:
            return
        base = LICENSE_OFFSETS[idx]
        self.content[base:base+LICENSE_SIZE] = b'\x00' * LICENSE_SIZE
        self._refresh_all()
        messagebox.showinfo("Deleted", f"License {idx+1} cleared.")

    def blank_license(self):
        idx = self._select_license("Blank license #")
        if idx is None:
            return
        base = LICENSE_OFFSETS[idx]
        blk = bytearray(LICENSE_SIZE)
        blk[:4] = b'RKPD'
        self.content[base:base+LICENSE_SIZE] = blk
        self._refresh_all()
        messagebox.showinfo("Blanked", f"License {idx+1} blanked.")


    def recompute_crcs(self):
        for l in range(4): self._apply_dwc(l)
        self._write_global_crc(); messagebox.showinfo("CRC","Done")

    def _refresh_all(self):
        for lic in range(4):
            self._load_dwc(lic)
            self._load_friends(lic)
            self._load_records(lic)
            self._load_cups(lic)
            self._load_unlocks(lic)
            self._load_favorites(lic)

    def _load_dwc(self, lic):
        base = LICENSE_OFFSETS[lic] + DWC_OFFSET
        for _,off in DWC_FIELDS:
            v = struct.unpack_from('>I', self.content, base+off)[0]
            self.dwc_vars[(lic,off)].set(str(v))
            if off==0x1C: self.fc_vars[lic].set(pid_to_friend_code(v))

    def _apply_dwc(self, lic):
        base = LICENSE_OFFSETS[lic] + DWC_OFFSET
        for _,off in DWC_FIELDS:
            try: val=int(self.dwc_vars[(lic,off)].get())
            except: return messagebox.showerror("Error","Fields must int")
            struct.pack_into('>I',self.content, base+off, val)
        blk = self.content[base:base+DWC_DATA_LEN]
        crc = reverse_crc32(blk)
        struct.pack_into('>I', self.content, base+DWC_DATA_LEN, crc)
        try: self.fc_vars[lic].set(pid_to_friend_code(int(self.dwc_vars[(lic,0x1C)].get())))
        except: pass

    def _load_friends(self, lic):
        tv = self.friend_views[lic]
        tv.delete(*tv.get_children())
        base = LICENSE_OFFSETS[lic] + FRIEND_MAIN_OFFSET
        for i in range(NUM_FRIENDS):
            ptr = base + i*FRIEND_STRIDE
            chunk = self.content[ptr:ptr+0x1A]
            pid = struct.unpack_from('>I',chunk,4)[0]
            wins = struct.unpack_from('>H',chunk,0x14)[0]
            losses = struct.unpack_from('>H',chunk,0x12)[0]
            race = struct.unpack_from('>H',chunk,0x16)[0]
            battle = struct.unpack_from('>H',chunk,0x18)[0]
            tv.insert('', 'end', values=(i+1,pid,pid_to_friend_code(pid),wins,losses,race,battle))

    def _load_records(self, lic):
        base = LICENSE_OFFSETS[lic]
        for (l,off),(vvar,typ) in self.record_vars.items():
            if l!=lic: continue
            fmt = '>'+typ if typ in ('H','I','i','f') else '<f'
            raw = struct.unpack_from(fmt, self.content, base+off)[0]
            display = int(raw) if typ=='f' else raw
            vvar.set(str(display))

    def _apply_records(self, lic):
        base = LICENSE_OFFSETS[lic]
        for (l,off),(vvar,typ) in self.record_vars.items():
            if l!=lic: continue
            try:
                val=float(vvar.get()) if typ=='f' else int(vvar.get())
            except ValueError:
                messagebox.showerror("Error",f"Record at 0x{off:X} must be number")
                return
            fmt='>'+typ
            struct.pack_into(fmt, self.content, base+off, val)
        messagebox.showinfo("Records",f"Records updated for license {lic+1}")

    def _load_cups(self,lic):
        base=LICENSE_OFFSETS[lic]
        for (l,off),(tvar,rvar,cvar) in self.cup_vars.items():
            if l!=lic:continue
            b4f=self.content[base+off+0x4F]&0x3; tvar.set(TROPHY_TYPES[b4f])
            rb=self.content[base+off+0x51]&0xF; rvar.set(STAR_RANKS[rb])
            comp=(self.content[base+off+0x52]&0x80)!=0; cvar.set(int(comp))

    def _apply_cups(self, lic):
        base = LICENSE_OFFSETS[lic]
        for (l, off), (tvar, rvar, cvar) in self.cup_vars.items():
            if l != lic: continue
            # Trophy
            try:
                t = TROPHY_TYPES.index(tvar.get())
            except ValueError:
                t = 3
            origb = self.content[base+off+0x4F]
            self.content[base+off+0x4F] = (origb & ~0x3) | t
            # Rank low nibble
            try:
                r = STAR_RANKS.index(rvar.get())
            except ValueError:
                r = 0
            origr = self.content[base+off+0x51]
            self.content[base+off+0x51] = (origr & 0xF0) | r
            # Completion high bit
            origc = self.content[base+off+0x52]
            comp = cvar.get() << 7
            self.content[base+off+0x52] = (origc & 0x7F) | comp
        messagebox.showinfo("Cups", f"Cups updated for license {lic+1}")

    def _preset_cup_ranks(self, lic, rank_idx):
        # Set trophy to Gold, star rank, and completion for all cups in a license
        for (l, off), (tvar, rvar, cvar) in self.cup_vars.items():
            if l != lic:
                continue
            tvar.set("Gold")
            rvar.set(STAR_RANKS[rank_idx])
            cvar.set(1)

    def _clear_all_cups(self, lic):
        # Set all cups to None, 'F', and unchecked
        for (l, off), (tvar, rvar, cvar) in self.cup_vars.items():
            if l != lic:
                continue
            tvar.set("None")
            rvar.set(STAR_RANKS[-1])  # 'F'
            cvar.set(0)

    def _build_unlocks_viewer(self, lic):
        """Build the Unlocks tab with grouped sections for Cups, Characters, and Vehicles."""
        f = ttk.Frame(self.notebook, padding=5)

        # Cup Completions Group: 0x30.*, 0x31.*, and 0x32 bits 0–1
        cup_frame = ttk.Labelframe(f, text="Cup Completions", padding=5)
        cup_frame.grid(row=0, column=0, sticky='nw', padx=5, pady=5)
        col = 0
        row = 0
        for label, off, bit in UNLOCK_FLAGS:
            if off in (0x30, 0x31) or (off == 0x32 and bit in (0, 1)):
                cb = ttk.Checkbutton(
                    cup_frame,
                    text=label,
                    variable=self._get_unlock_var(lic, off, bit)
                )
                cb.grid(row=row, column=col, sticky='w', padx=2, pady=2)
                col += 1
                if col >= 2:
                    col = 0
                    row += 1

        # Character Unlocks Group: 0x32 bits 2–7 and all of 0x33
        char_frame = ttk.Labelframe(f, text="Character Unlocks", padding=5)
        char_frame.grid(row=0, column=1, sticky='nw', padx=5, pady=5)
        col = 0
        row = 0
        for label, off, bit in UNLOCK_FLAGS:
            if (off == 0x32 and bit >= 2) or off == 0x33:
                cb = ttk.Checkbutton(
                    char_frame,
                    text=label,
                    variable=self._get_unlock_var(lic, off, bit)
                )
                cb.grid(row=row, column=col, sticky='w', padx=2, pady=2)
                col += 1
                if col >= 2:
                    col = 0
                    row += 1

        # Vehicle Unlocks Group: 0x35, 0x36, 0x37
        veh_frame = ttk.Labelframe(f, text="Vehicle Unlocks", padding=5)
        veh_frame.grid(row=1, column=0, columnspan=2, sticky='nw', padx=5, pady=5)
        col = 0
        row = 0
        for label, off, bit in UNLOCK_FLAGS:
            if off in (0x35, 0x36, 0x37):
                cb = ttk.Checkbutton(
                    veh_frame,
                    text=label,
                    variable=self._get_unlock_var(lic, off, bit)
                )
                cb.grid(row=row, column=col, sticky='w', padx=2, pady=2)
                col += 1
                if col >= 4:
                    col = 0
                    row += 1

        # Buttons
        total_rows = max(row + 1, 3)
        btn_frame = ttk.Frame(f)
        btn_frame.grid(row=total_rows, column=0, columnspan=2, pady=10)
        ttk.Button(
            btn_frame,
            text="Unlock All",
            command=lambda l=lic: self._unlock_all(l)
        ).pack(side='left', padx=5)
        ttk.Button(
            btn_frame,
            text="Apply Unlocks",
            command=lambda l=lic: self._apply_unlocks(l)
        ).pack(side='left', padx=5)

        return f


    def _get_unlock_var(self, lic, off, bit):
        key = (lic, off, bit)
        if key not in self.unlock_vars:
            self.unlock_vars[key] = tk.IntVar()
        return self.unlock_vars[key]

    def _load_unlocks(self, lic):
        base = LICENSE_OFFSETS[lic]
        for (l, off, bit), var in self.unlock_vars.items():
            if l != lic: continue
            byte = self.content[base + off]
            var.set(1 if (byte >> bit) & 1 else 0)

    def _apply_unlocks(self, lic):
        base = LICENSE_OFFSETS[lic]
        # write all bits from the UI to the save
        for (l, off, bit), var in self.unlock_vars.items():
            if l != lic:
                continue
            orig = self.content[base + off]
            if var.get():
                self.content[base + off] = orig | (1 << bit)
            else:
                self.content[base + off] = orig & ~(1 << bit)

        # After writing, enforce unlock criteria for Spear and Sprinter if needed
        # Spear: 12 expert ghosts, OR 200 WFC wins, OR 3600 races
        self._check_vehicle_requirements(
            lic,
            vehicle_name="Spear",
            off=0x35,
            bit=5,
            required_expert=12,
            required_wfc_wins=200,
            required_races=3600,
        )
        # Sprinter: 24 expert ghosts, OR 3000 WFC wins, OR 4650 races
        self._check_vehicle_requirements(
            lic,
            vehicle_name="Sprinter",
            off=0x37,
            bit=0,
            required_expert=24,
            required_wfc_wins=3000,
            required_races=4650,
        )

        messagebox.showinfo("Unlocks", f"Unlock flags applied for license {lic+1}")

    def _check_vehicle_requirements(
        self,
        lic,
        vehicle_name,
        off,
        bit,
        required_expert,
        required_wfc_wins,
        required_races,
    ):
        """
        If the given vehicle bit is set but none of its unlock criteria are met,
        prompt the user and optionally modify ghost flags / WFC wins / races.
        """
        base = LICENSE_OFFSETS[lic]

        # Only care if the vehicle bit is actually 1 after applying unlocks
        if not (self.content[base + off] & (1 << bit)):
            return

        # Count expert staff ghosts (4 bytes at 0x10)
        exp_flags = self.content[base + 0x10 : base + 0x14]
        expert_count = sum(bin(b).count("1") for b in exp_flags)

        # WFC Wins (VS Race) at 0x98, Int32
        wfc_wins = struct.unpack_from('>i', self.content, base + 0x98)[0]

        # Total Race Count at 0xB4, Int32
        total_races = struct.unpack_from('>i', self.content, base + 0xB4)[0]

        # If any criterion is already met, nothing to do
        if (
            expert_count >= required_expert
            or wfc_wins >= required_wfc_wins
            or total_races >= required_races
        ):
            return

        # Otherwise, ask user how they want to satisfy one of the criteria
        choice = self._prompt_vehicle_unlock_action(
            lic=lic,
            vehicle_name=vehicle_name,
            expert_count=expert_count,
            wfc_wins=wfc_wins,
            total_races=total_races,
            required_expert=required_expert,
            required_wfc_wins=required_wfc_wins,
            required_races=required_races,
        )

        if choice == "ghosts":
            # Complete all normal + expert staff ghost flags for this license
            norm_off = base + 0x0C
            exp_off = base + 0x10
            self.content[norm_off : norm_off + 4] = b'\xFF' * 4
            self.content[exp_off : exp_off + 4] = b'\xFF' * 4

        elif choice == "wfc":
            # Bump WFC wins up to at least required + 1
            target = required_wfc_wins + 1
            new_wins = max(wfc_wins, target)
            struct.pack_into('>i', self.content, base + 0x98, new_wins)

        elif choice == "races":
            # Bump total races up to at least required + 1
            target = required_races + 1
            new_races = max(total_races, target)
            struct.pack_into('>i', self.content, base + 0xB4, new_races)

        # choice == "cancel": do nothing extra – bit stays set, stats unchanged

    def _prompt_vehicle_unlock_action(
        self,
        lic,
        vehicle_name,
        expert_count,
        wfc_wins,
        total_races,
        required_expert,
        required_wfc_wins,
        required_races,
    ):
        """
        Show a modal dialog explaining that no unlock criteria are met for
        the given vehicle and ask how to satisfy one of them.

        Returns one of: "ghosts", "wfc", "races", "cancel".
        """
        dlg = tk.Toplevel(self.root)
        dlg.title(f"{vehicle_name} unlock requirements")
        dlg.transient(self.root)
        dlg.grab_set()

        msg = (
            f"No unlock condition is currently met for {vehicle_name} on license {lic+1}.\n\n"
            f"{vehicle_name} can be unlocked by any of:\n"
            f"- {required_expert} Expert Staff Ghosts (current: {expert_count})\n"
            f"- {required_wfc_wins} WFC VS race wins (current: {wfc_wins})\n"
            f"- {required_races} total races (current: {total_races})\n\n"
            "Choose how you want the editor to satisfy one condition automatically:"
        )

        ttk.Label(dlg, text=msg, justify='left', wraplength=480).grid(
            row=0, column=0, columnspan=4, padx=10, pady=10
        )

        choice = tk.StringVar(value="cancel")

        def set_choice(val):
            choice.set(val)
            dlg.destroy()

        ttk.Button(dlg, text="Ghosts",   command=lambda: set_choice("ghosts")) \
            .grid(row=1, column=0, padx=5, pady=5)
        ttk.Button(dlg, text="WFC wins", command=lambda: set_choice("wfc")) \
            .grid(row=1, column=1, padx=5, pady=5)
        ttk.Button(dlg, text="Races",    command=lambda: set_choice("races")) \
            .grid(row=1, column=2, padx=5, pady=5)
        ttk.Button(dlg, text="Cancel",   command=lambda: set_choice("cancel")) \
            .grid(row=1, column=3, padx=5, pady=5)

        dlg.wait_window()
        return choice.get()



    def _unlock_all(self, lic):
        # Set every unlock flag to 1 in UI
        for (l, off, bit), var in self.unlock_vars.items():
            if l == lic:
                var.set(1)

    def _export_friends(self):
        idx = self._select_license("Export friends for license #")
        if idx is None: return
        fn = filedialog.asksaveasfilename(defaultextension='.csv', filetypes=[("CSV","*.csv")])
        if not fn: return
        base = LICENSE_OFFSETS[idx] + FRIEND_MAIN_OFFSET
        with open(fn, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            # Header
            header = ["Slot"] + [name for name,_,_ in FRIEND_FIELDS]
            writer.writerow(header)
            # Rows
            for i in range(NUM_FRIENDS):
                ptr = base + i * FRIEND_STRIDE
                row = [i+1]
                for name, off, fmt in FRIEND_FIELDS:
                    size = struct.calcsize(fmt)
                    raw = self.content[ptr+off:ptr+off+size]
                    if fmt.endswith('s'):
                        val = raw.hex().upper()
                    else:
                        val = struct.unpack_from('>' + fmt, self.content, ptr+off)[0]
                    row.append(val)
                writer.writerow(row)
        messagebox.showinfo("Exported", f"Friends exported to {fn}")

    def _import_friends(self):
        idx = self._select_license("Import friends for license #")
        if idx is None: return
        fn = filedialog.askopenfilename(filetypes=[("CSV","*.csv")])
        if not fn: return
        base = LICENSE_OFFSETS[idx] + FRIEND_MAIN_OFFSET
        with open(fn, newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                try:
                    slot = int(row["Slot"]) - 1
                except:
                    continue
                ptr = base + slot * FRIEND_STRIDE
                # Rebuild block
                for name, off, fmt in FRIEND_FIELDS:
                    if fmt.endswith('s'):
                        data = bytes.fromhex(row[name])
                        self.content[ptr+off:ptr+off+len(data)] = data
                    else:
                        val = int(row[name])
                        struct.pack_into('>' + fmt, self.content, ptr+off, val)
        self._load_friends(idx)
        messagebox.showinfo("Imported", f"Friends imported from {fn}")

    def _change_region(self):
        # Swap the save-file region code
        try:
            current = struct.unpack_from('>H', self.content, REGION_ID_OFFSET)[0]
        except Exception:
            messagebox.showerror("Error", "Failed to read region ID")
            return
        inv_map = {v:k for k,v in REGION_IDS.items()}
        current_name = inv_map.get(current, list(REGION_IDS.keys())[0])
        dlg = tk.Toplevel(self.root)
        dlg.title("Change Region")
        ttk.Label(dlg, text="Select Region:").grid(row=0, column=0, padx=5, pady=5)
        region_var = tk.StringVar(value=current_name)
        cb = ttk.Combobox(dlg, values=list(REGION_IDS.keys()), textvariable=region_var, state='readonly')
        cb.grid(row=0, column=1, padx=5, pady=5)
        btn_frame = ttk.Frame(dlg)
        btn_frame.grid(row=1, column=0, columnspan=2, pady=10)
        def on_ok():
            sel = region_var.get()
            val = REGION_IDS.get(sel, 0)
            struct.pack_into('>H', self.content, REGION_ID_OFFSET, val)
            self._write_global_crc()
            messagebox.showinfo("Region", f"Region changed to {sel}")
            dlg.destroy()
        ttk.Button(btn_frame, text="OK", command=on_ok).pack(side='left', padx=5)
        ttk.Button(btn_frame, text="Cancel", command=dlg.destroy).pack(side='left', padx=5)

    def _complete_normal_staff(self):
        # Prompt for license
        idx = self._select_license("Complete normal staff ghosts for license #")
        if idx is None:
            return
        base = LICENSE_OFFSETS[idx]
        # Set normal staff ghost flags (4 bytes at offset 0x0C) to all 1s for selected license
        off = base + 0x0C
        self.content[off:off+4] = b'\xFF' * 4
        self._write_global_crc()
        messagebox.showinfo("Ghosts", f"Normal staff ghost flags completed for license {idx+1}.")

    def _complete_expert_staff(self):
        # Prompt for license
        idx = self._select_license("Complete expert staff ghosts for license #")
        if idx is None:
            return
        base = LICENSE_OFFSETS[idx]
        # Set expert staff ghost flags (4 bytes at offset 0x10) to all 1s for selected license
        off = base + 0x10
        self.content[off:off+4] = b'\xFF' * 4
        self._write_global_crc()
        messagebox.showinfo("Ghosts", f"Expert staff ghost flags completed for license {idx+1}.")

    def _build_favorite_viewer(self, lic, items, title):
        f = ttk.Frame(self.notebook, padding=5)
        # Two-column grid
        for idx, (lbl, off) in enumerate(items):
            row = idx // 2
            col = (idx % 2) * 2
            ttk.Label(f, text=lbl).grid(row=row, column=col, sticky='e', padx=5, pady=2)
            var = tk.StringVar()
            ttk.Entry(f, textvariable=var, width=12).grid(row=row, column=col+1, padx=5, pady=2)
            self.fav_vars[(lic, off)] = var
        # Apply button
        total_rows = (len(items)+1)//2
        btn = ttk.Button(f, text=f"Apply {title}", command=lambda l=lic, it=items: self._apply_favorites(l, it))
        btn.grid(row=total_rows, column=0, columnspan=4, pady=10)
        return f

    def _load_favorites(self, lic):
        base = LICENSE_OFFSETS[lic]
        for (l, off), var in self.fav_vars.items():
            if l != lic: continue
            val = struct.unpack_from('>H', self.content, base+off)[0]
            var.set(str(val))

    def _apply_favorites(self, lic, items):
        base = LICENSE_OFFSETS[lic]
        for lbl, off in items:
            var = self.fav_vars[(lic, off)]
            try:
                v = int(var.get())
            except ValueError:
                messagebox.showerror("Error", f"{lbl} must be an integer")
                return
            struct.pack_into('>H', self.content, base+off, v)
        messagebox.showinfo(title="Favorites", message=f"Favorites updated for license {lic+1}")

    def show_global_crc(self):
        # Show the 4-byte stored CRC at GLOBAL_CRC_OFFSET in hex
        if not self.content:
            messagebox.showerror("Error", "No save file loaded.")
            return
        # stored big-endian
        crc = struct.unpack_from('>I', self.content, GLOBAL_CRC_OFFSET)[0]
        messagebox.showinfo("Global CRC", f"Stored global CRC: 0x{crc:08X}")

    def _write_global_crc(self):
        c = compute_global_crc(self.content)
        struct.pack_into('>I', self.content, GLOBAL_CRC_OFFSET, c)

if __name__ == '__main__':
    SaveEditorApp()
