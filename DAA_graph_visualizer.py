"""
DAA Graph Visualizer
--------------------
A graph-only visualizer with step-by-step / automatic BFS and DFS traversal.
Graphs can be directed (arrows) or undirected (plain lines), and weighted
(optional weight per edge) or unweighted - the two options are independent.

Run:  python graph_visualizer.py
Needs only the Python standard library (Tkinter).
On Linux, if Tkinter is missing:  sudo apt install python3-tk

Controls
  * Click empty canvas ........ add a vertex
  * Click vertex A, then B .... draw edge A-B (arrow if Directed; asks for a
                                weight if Weighted - leave empty for none)
  * Click the same vertex ..... deselect it
  * Drag a vertex ............. move it
  * Double-click / right-click  delete a vertex (or Delete key on a selected one)
"""

import colorsys
import math
import random
import tkinter as tk
from collections import deque
from tkinter import messagebox, simpledialog, ttk

NODE_R = 22

COL = {
    "bg": "#eef3f9",            # canvas background
    "node": "#e3f2fd",          # unvisited vertex
    "node_outline": "#455a64",
    "current": "#ff9800",       # vertex being visited right now
    "selected": "#1e88e5",
    "edge": "#90a4ae",
    "weight_bg": "#f3e5f5",
    "weight_border": "#ab47bc",
    "weight_text": "#6a1b9a",
    "text": "#1a237e",
    "banner": "#2e7d32",
}

CONFETTI = ["#ef5350", "#ab47bc", "#42a5f5", "#26c6da", "#66bb6a",
            "#ffee58", "#ffa726", "#ec407a"]


# colour + heading used for each kind of step in the explanation panel
KIND_STYLE = {
    "visit": ("#2e7d32", "VISIT"),
    "process": ("#3949ab", "PROCESS"),
    "skip": ("#e53935", "SKIP"),
    "backtrack": ("#8e24aa", "BACKTRACK"),
    "done": ("#2e7d32", "DONE"),
}
RING_FOCUS = "#3949ab"


def hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def rgb_to_hex(rgb):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(round(c)))) for c in rgb)


def blend(c1, c2, t):
    """Mix colour c1 into c2 (t=0 -> c1, t=1 -> c2). Used to fake transparency."""
    a, b = hex_to_rgb(c1), hex_to_rgb(c2)
    return rgb_to_hex([a[i] + (b[i] - a[i]) * t for i in range(3)])


def shade(c, factor):
    """factor < 1 darkens a colour."""
    return rgb_to_hex([ch * factor for ch in hex_to_rgb(c)])


def order_color(i, n):
    """Colour of the i-th visited vertex out of n: a cyan -> green -> yellow -> orange
    rainbow, so the visiting order can be read straight from the colours."""
    t = i / max(n - 1, 1)
    hue = 0.52 - 0.47 * t          # 0.52 = cyan ... 0.05 = orange
    r, g, b = colorsys.hsv_to_rgb(hue, 0.55, 0.96)
    return rgb_to_hex((r * 255, g * 255, b * 255))


NUMBER_START = 0   # first vertex number in "Numbers" mode (change to 1 if you prefer 1..n)
MAX_LABEL_LEN = 4  # longest custom vertex name that still fits inside the circle


def letters_name(n):
    """0 -> A, 1 -> B, ... 25 -> Z, 26 -> AA, 27 -> AB ..."""
    n += 1
    s = ""
    while n > 0:
        n, r = divmod(n - 1, 26)
        s = chr(65 + r) + s
    return s


def fmt_w(w):
    if w is None:
        return ""
    w = float(w)
    return str(int(w)) if w.is_integer() else f"{w:g}"


class GraphVisualizer:
    def __init__(self, root):
        self.root = root
        root.title("DAA Graph Visualizer")
        root.geometry("1280x740")

        # ---- graph data ----
        self.vertices = {}        # id -> (x, y)
        self.labels = {}          # id -> display name (letters, numbers or custom text)
        self.vertex_history = []  # order vertices were added (for Undo Vertex)
        self.edges = {}           # (u, v) -> weight (or None)
        self.edge_history = []    # order edges were added (for undo)
        self.selected = None      # source vertex waiting for a destination

        # ---- mouse state ----
        self.press_vertex = None
        self.press_xy = (0, 0)
        self.dragged = False
        self.mouse_xy = None      # last mouse position (for the preview arrow)

        # ---- traversal state ----
        self.steps = None         # list of (vertex, via_edge)
        self.step_index = 0
        self.visit_order = []
        self.tree_edges = set()
        self.current = None
        self.auto = False
        self.after_id = None
        self.label_to_id = {}

        # ---- visual effects ----
        self.current_via = None   # edge used to reach the current vertex (animated)
        self.finished = False     # traversal complete -> show result banner
        self.celebrating = False  # confetti + rainbow wave running
        self.celebrate_start = 0.0
        self.confetti = []
        self.rings = {}           # vertex -> ring colour (processing / skipped / backtrack)
        self.hl_edge = None       # edge highlighted by the current step
        self.hl_kind = None       # kind of that step ("skip" / "backtrack")
        self.phase = 0.0          # 0..1, drives the pulsing / flowing animations
        self.clock = 0.0          # seconds since the animation loop started
        self.anim_id = None

        self.build_ui()
        self.refresh_start_choices()
        self.log_intro()
        self.redraw()

    # ------------------------------------------------------------------ UI
    def setup_styles(self):
        bg = "#dfe8f3"
        self.root.configure(bg=bg)
        st = ttk.Style()
        try:
            st.theme_use("clam")      # the only built-in theme that lets buttons be coloured
        except tk.TclError:
            pass
        st.configure("TFrame", background=bg)
        st.configure("TLabel", background=bg, foreground="#263238")
        st.configure("TCheckbutton", background=bg, foreground="#263238")
        st.map("TCheckbutton", background=[("active", bg)])

        def accent(name, color):
            st.configure(name, background=color, foreground="white", padding=(10, 4),
                         borderwidth=0, focusthickness=0, font=("Segoe UI", 9, "bold"))
            st.map(name, background=[("pressed", shade(color, 0.7)),
                                     ("active", shade(color, 0.85))],
                   foreground=[("active", "white")])

        accent("Tool.TButton", "#607d8b")
        accent("Danger.TButton", "#e53935")
        accent("Step.TButton", "#1e88e5")
        accent("Go.TButton", "#43a047")
        accent("Warn.TButton", "#fb8c00")

    def build_ui(self):
        self.setup_styles()
        # Row 1: graph editing
        top = ttk.Frame(self.root, padding=(8, 6))
        top.pack(fill="x")

        self.directed = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Directed (arrows)", variable=self.directed,
                        command=self.on_directed_toggle).pack(side="left", padx=4)

        self.weighted = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Weighted", variable=self.weighted,
                        command=self.on_weighted_toggle).pack(side="left", padx=4)

        self.delete_mode = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="Delete vertex mode", variable=self.delete_mode,
                        command=self.on_mode_change).pack(side="left", padx=4)

        ttk.Label(top, text="Vertex names:").pack(side="left", padx=(12, 2))
        self.label_mode = tk.StringVar(value="Letters")
        mode_box = ttk.Combobox(top, textvariable=self.label_mode, width=9, state="readonly",
                                values=["Letters", "Numbers", "Custom"])
        mode_box.pack(side="left", padx=(0, 8))
        mode_box.bind("<<ComboboxSelected>>", lambda e: self.on_label_mode_change())

        ttk.Button(top, text="Undo Vertex", style="Tool.TButton",
                   command=self.undo_vertex).pack(side="left", padx=4)
        ttk.Button(top, text="Undo Edge", style="Tool.TButton",
                   command=self.undo_edge).pack(side="left", padx=4)
        ttk.Button(top, text="Clear Canvas", style="Danger.TButton",
                   command=self.clear_canvas).pack(side="left", padx=4)

        # Row 2: traversal
        bar = ttk.Frame(self.root, padding=(8, 0, 8, 6))
        bar.pack(fill="x")

        ttk.Label(bar, text="Algorithm:").pack(side="left")
        self.algo_var = tk.StringVar(value="BFS")
        algo = ttk.Combobox(bar, textvariable=self.algo_var, values=["BFS", "DFS"],
                            width=6, state="readonly")
        algo.pack(side="left", padx=(4, 10))
        algo.bind("<<ComboboxSelected>>", lambda e: self.reset_traversal())

        ttk.Label(bar, text="Start vertex:").pack(side="left")
        self.start_var = tk.StringVar()
        self.start_box = ttk.Combobox(bar, textvariable=self.start_var, width=6,
                                      state="readonly")
        self.start_box.pack(side="left", padx=(4, 10))
        self.start_box.bind("<<ComboboxSelected>>", lambda e: self.reset_traversal())

        self.all_components = tk.BooleanVar(value=False)
        ttk.Checkbutton(bar, text="Visit all components", variable=self.all_components,
                        command=self.reset_traversal).pack(side="left", padx=4)

        self.show_panel = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar, text="Show explanation", variable=self.show_panel,
                        command=self.toggle_panel).pack(side="left", padx=4)

        ttk.Button(bar, text="Step ▶", style="Step.TButton",
                   command=self.step).pack(side="left", padx=4)
        self.auto_btn = ttk.Button(bar, text="Auto Play", style="Go.TButton",
                                   command=self.toggle_auto)
        self.auto_btn.pack(side="left", padx=4)
        ttk.Button(bar, text="Reset", style="Warn.TButton",
                   command=self.reset_traversal).pack(side="left", padx=4)

        ttk.Label(bar, text="Speed:").pack(side="left", padx=(12, 2))
        self.speed = tk.Scale(bar, from_=1, to=10, orient="horizontal", length=110,
                              showvalue=False, bg="#dfe8f3", highlightthickness=0,
                              troughcolor="#90caf9", activebackground="#1e88e5")
        self.speed.set(5)
        self.speed.pack(side="left")

        # Main area: graph canvas on the left, explanation panel on the right
        self.body = ttk.PanedWindow(self.root, orient="horizontal")
        self.body.pack(fill="both", expand=True, padx=8)

        self.canvas = tk.Canvas(self.body, bg=COL["bg"], highlightthickness=1,
                                highlightbackground="#90a4ae")
        self.body.add(self.canvas, weight=4)

        self.panel = ttk.Frame(self.body)
        self.body.add(self.panel, weight=1)
        self.build_panel()
        self.canvas.bind("<Motion>", self.on_hover)
        self.canvas.bind("<Leave>", self.on_leave)
        self.canvas.bind("<Double-Button-1>", self.on_double_click)
        self.root.bind("<Delete>", self.on_delete_key)
        self.root.bind("<BackSpace>", self.on_delete_key)
        self.canvas.bind("<Button-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_motion)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<Button-2>", self.on_right_click)  # macOS right-click

        # Bottom: status + traversal output
        bottom = ttk.Frame(self.root, padding=8)
        bottom.pack(fill="x")
        self.status = tk.StringVar(value="Click on the canvas to add a vertex.")
        ttk.Label(bottom, textvariable=self.status, foreground="#455a64").pack(anchor="w")
        self.output = tk.StringVar(value="Traversal order: –")
        ttk.Label(bottom, textvariable=self.output, font=("Segoe UI", 12, "bold"),
                  foreground="#1565c0", wraplength=1050,
                  justify="left").pack(anchor="w", pady=(4, 0))

    def set_status(self, msg):
        self.status.set(msg)

    # ------------------------------------------------- explanation panel
    def build_panel(self):
        ttk.Label(self.panel, text="Step-by-step explanation",
                  font=("Segoe UI", 12, "bold"),
                  foreground="#1a237e").pack(anchor="w", padx=6, pady=(2, 0))

        legend = ttk.Frame(self.panel)
        legend.pack(fill="x", padx=6, pady=(2, 4))
        items = [("●", COL["current"], "visiting now"),
                 ("◯", RING_FOCUS, "being processed"),
                 ("◯", KIND_STYLE["skip"][0], "skipped (already visited)"),
                 ("◯", KIND_STYLE["backtrack"][0], "backtrack")]
        for i, (sym, color, text) in enumerate(items):
            f = ttk.Frame(legend)
            f.grid(row=i // 2, column=i % 2, sticky="w", padx=(0, 10))
            ttk.Label(f, text=sym, foreground=color,
                      font=("Segoe UI", 11, "bold")).pack(side="left")
            ttk.Label(f, text=text, font=("Segoe UI", 8)).pack(side="left", padx=(2, 0))

        wrap = ttk.Frame(self.panel)
        wrap.pack(fill="both", expand=True, padx=(6, 0), pady=(0, 4))
        self.log = tk.Text(wrap, wrap="word", width=40, state="disabled", bg="#ffffff",
                           relief="flat", padx=10, pady=8, font=("Segoe UI", 10),
                           cursor="arrow", highlightthickness=1,
                           highlightbackground="#b0bec5")
        sb = ttk.Scrollbar(wrap, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.log.pack(side="left", fill="both", expand=True)

        self.log.tag_configure("heading", font=("Segoe UI", 12, "bold"),
                               foreground="#1a237e")
        self.log.tag_configure("title", font=("Segoe UI", 10, "bold"), spacing1=2)
        for kind, (color, _) in KIND_STYLE.items():
            self.log.tag_configure(f"t_{kind}", foreground=color)
        self.log.tag_configure("body", spacing3=2)
        self.log.tag_configure("ds", font=("Courier New", 10, "bold"),
                               foreground="#37474f", background="#eceff1",
                               lmargin1=6, lmargin2=6)
        self.log.tag_configure("latest", background="#fff8e1")  # newest step is highlighted

    def toggle_panel(self):
        if self.show_panel.get():
            self.body.add(self.panel, weight=1)
        else:
            self.body.forget(self.panel)

    def log_clear(self):
        self.log.configure(state="normal")
        self.log.delete("1.0", "end")
        self.log.configure(state="disabled")

    def log_intro(self):
        """Text shown before the first step."""
        self.log_clear()
        self.log.configure(state="normal")
        if self.algo_var.get() == "BFS":
            self.log.insert("end", "Breadth-First Search (BFS)\n", "heading")
            self.log.insert("end",
                "Explores the graph level by level using a QUEUE (first in, first out): "
                "first every vertex one edge away from the start, then two edges away, "
                "and so on.\n\n", "body")
        else:
            self.log.insert("end", "Depth-First Search (DFS)\n", "heading")
            self.log.insert("end",
                "Goes as deep as possible along one path using a STACK (the recursion "
                "stack). When a vertex has nothing new left, it backtracks to the "
                "previous vertex and tries its next neighbor.\n\n", "body")
        if not self.vertices:
            self.log.insert("end", "Add vertices and edges on the canvas first.\n", "body")
        else:
            self.log.insert("end",
                "Press Step ▶ or Auto Play. Every action is written here as its own "
                "numbered step, and the graph is never covered. Neighbors are checked "
                "in the order the vertices were created.\n", "body")
        self.log.configure(state="disabled")

    def log_add(self, n, total, e):
        t = self.log
        t.configure(state="normal")
        if n == 1:
            t.delete("1.0", "end")      # replace the intro with the first step
        t.tag_remove("latest", "1.0", "end")
        start = t.index("end-1c")
        t.insert("end", f"Step {n}/{total} · {e['title']}\n", ("title", f"t_{e['kind']}"))
        t.insert("end", e["detail"] + "\n", "body")
        if e["ds"]:
            t.insert("end", e["ds"] + "\n", "ds")
        t.insert("end", "\n")
        t.tag_add("latest", start, "end-1c")
        t.see("end")
        t.configure(state="disabled")

    def on_mode_change(self):
        self.selected = None
        if self.delete_mode.get():
            self.set_status("Delete mode: click a vertex to remove it.")
        else:
            self.set_status("Click empty space to add a vertex; click two vertices to draw an arrow.")
        self.redraw()

    # ------------------------------------------------------- vertex helpers
    def vertex_at(self, x, y):
        for v, (vx, vy) in self.vertices.items():
            if math.hypot(x - vx, y - vy) <= NODE_R:
                return v
        return None

    def new_id(self):
        i = 0
        while i in self.vertices:
            i += 1
        return i

    def label(self, v):
        return self.labels.get(v, "?")

    def sep(self):
        """Arrow for directed graphs, plain dash for undirected."""
        return "→" if self.directed.get() else "—"

    def on_label_mode_change(self):
        mode = self.label_mode.get()
        hints = {
            "Letters": "New vertices will be named A, B, C, ...",
            "Numbers": f"New vertices will be named {NUMBER_START}, {NUMBER_START + 1}, "
                       f"{NUMBER_START + 2}, ...",
            "Custom": "You will be asked to type a name (letters and/or numbers) for each "
                      "new vertex.",
        }
        self.set_status(hints[mode] + " Existing vertices keep their names.")

    def make_label(self):
        """Name for the next vertex, or None if the user cancelled."""
        used = set(self.labels.values())
        mode = self.label_mode.get()
        if mode == "Letters":
            i = 0
            while letters_name(i) in used:
                i += 1
            return letters_name(i)
        if mode == "Numbers":
            i = NUMBER_START
            while str(i) in used:
                i += 1
            return str(i)
        # Custom: ask until the name is valid or the user cancels
        prompt = f"Vertex name (letters and/or numbers, up to {MAX_LABEL_LEN} characters):"
        while True:
            name = simpledialog.askstring("New vertex", prompt, parent=self.root)
            if name is None:
                self.set_status("Vertex cancelled.")
                return None
            name = name.strip()
            if not name:
                prompt = "Name can't be empty. Enter a vertex name:"
            elif len(name) > MAX_LABEL_LEN:
                prompt = f"Too long - use at most {MAX_LABEL_LEN} characters:"
            elif name in used:
                prompt = f"'{name}' is already used. Enter a different name:"
            else:
                return name

    def add_vertex(self, x, y):
        w = max(self.canvas.winfo_width(), 200)
        h = max(self.canvas.winfo_height(), 200)
        x = min(max(x, NODE_R), w - NODE_R)
        y = min(max(y, NODE_R), h - NODE_R)
        for vx, vy in self.vertices.values():
            if math.hypot(x - vx, y - vy) < 2 * NODE_R:
                self.set_status("Too close to another vertex - click a bit further away.")
                return
        name = self.make_label()
        if name is None:
            return
        v = self.new_id()
        self.vertices[v] = (x, y)
        self.labels[v] = name
        self.vertex_history.append(v)
        self.selected = None
        self.refresh_start_choices()
        self.reset_traversal()
        self.set_status(f"Added vertex {self.label(v)}.")

    def delete_vertex(self, v):
        name = self.label(v)
        self.vertices.pop(v, None)
        self.labels.pop(v, None)
        self.vertex_history = [x for x in self.vertex_history if x != v]
        self.edges = {e: w for e, w in self.edges.items() if v not in e}
        self.edge_history = [e for e in self.edge_history if e in self.edges]
        self.selected = None
        self.refresh_start_choices()
        self.reset_traversal()
        self.set_status(f"Deleted vertex {name} and its edges.")

    # --------------------------------------------------------- edge helpers
    def edge_key(self, u, v):
        """Stored key of the edge between u and v (either direction if the graph
        is undirected), or None if there is no such edge."""
        if (u, v) in self.edges:
            return (u, v)
        if not self.directed.get() and (v, u) in self.edges:
            return (v, u)
        return None

    def add_edge(self, u, v):
        pair = f"{self.label(u)} {self.sep()} {self.label(v)}"
        key = self.edge_key(u, v)
        if key is not None:
            if self.weighted.get():
                ok, w = self.ask_weight(u, v, self.edges[key])
                if ok:
                    self.edges[key] = w
                    self.set_status(f"Updated weight of {pair}." if w is not None
                                    else f"Removed weight from {pair}.")
            else:
                self.set_status(f"Edge {pair} already exists.")
            self.redraw()
            return
        w = None
        if self.weighted.get():
            ok, w = self.ask_weight(u, v)
            if not ok:  # Cancel pressed
                self.set_status("Edge cancelled.")
                return
        self.edges[(u, v)] = w
        self.edge_history.append((u, v))
        self.reset_traversal()
        self.set_status(f"Added edge {pair}" + (f" (weight {fmt_w(w)})." if w is not None
                                                 else " (no weight)."))

    def ask_weight(self, u, v, current=None):
        """Ask for an edge weight. Returns (ok, weight):
        OK with a number -> (True, number); OK with an empty box -> (True, None)
        meaning "no weight on this edge"; Cancel -> (False, None)."""
        prompt = (f"Weight for {self.label(u)} {self.sep()} {self.label(v)}\n"
                  "(leave empty for no weight):")
        initial = fmt_w(current)
        while True:
            text = simpledialog.askstring("Edge weight", prompt, parent=self.root,
                                          initialvalue=initial)
            if text is None:
                return False, None
            text = text.strip()
            if text == "":
                return True, None
            try:
                w = float(text)
                if math.isfinite(w):
                    return True, w
            except ValueError:
                pass
            prompt = "That is not a number. Enter a number (or leave empty for no weight):"
            initial = text

    def undo_edge(self):
        if not self.edge_history:
            self.set_status("No edges to undo.")
            return
        e = self.edge_history.pop()
        self.edges.pop(e, None)
        self.reset_traversal()
        self.set_status(f"Removed edge {self.label(e[0])} {self.sep()} {self.label(e[1])}.")

    def clear_canvas(self):
        self.vertices.clear()
        self.labels.clear()
        self.vertex_history.clear()
        self.edges.clear()
        self.edge_history.clear()
        self.selected = None
        self.refresh_start_choices()
        self.reset_traversal()
        self.set_status("Canvas cleared.")

    def on_directed_toggle(self):
        """Directed = arrows (A→B differs from B→A); undirected = plain lines.
        The two kinds of edges are not interchangeable, so edges are cleared
        (vertices stay) when this option changes."""
        if self.edges:
            if not messagebox.askyesno(
                    "Change graph type",
                    "Switching between directed and undirected removes all existing "
                    "edges (vertices are kept). Continue?"):
                self.directed.set(not self.directed.get())  # revert the checkbox
                return
            self.edges.clear()
            self.edge_history.clear()
        self.selected = None
        self.reset_traversal()
        if self.directed.get():
            self.set_status("Directed graph: edges are arrows from source to destination.")
        else:
            self.set_status("Undirected graph: edges are plain lines (no arrows).")

    def on_weighted_toggle(self):
        """Weights are optional per edge and work for directed and undirected graphs."""
        self.reset_traversal()
        if self.weighted.get():
            self.set_status("Weighted: you will be asked for a weight on each new edge "
                            "(leave it empty for an edge with no weight).")
        else:
            self.set_status("Weights hidden. Turn Weighted back on to see or edit them.")

    def neighbors(self, u):
        nb = {v for (a, v) in self.edges if a == u}
        if not self.directed.get():
            nb |= {a for (a, v) in self.edges if v == u}
        return sorted(nb)

    # -------------------------------------------------------- mouse events
    def on_hover(self, event):
        self.mouse_xy = (event.x, event.y)
        if self.selected is not None and self.press_vertex is None:
            self.redraw()

    def on_leave(self, event):
        self.mouse_xy = None
        if self.selected is not None:
            self.redraw()

    def on_press(self, event):
        v = self.vertex_at(event.x, event.y)
        self.press_vertex = v
        self.press_xy = (event.x, event.y)
        self.dragged = False
        if v is None and not self.delete_mode.get():
            self.add_vertex(event.x, event.y)
            self.redraw()

    def on_motion(self, event):
        v = self.press_vertex
        if v is None or self.delete_mode.get():
            return
        if not self.dragged:
            if math.hypot(event.x - self.press_xy[0], event.y - self.press_xy[1]) > 4:
                self.dragged = True
            else:
                return
        w = max(self.canvas.winfo_width(), 200)
        h = max(self.canvas.winfo_height(), 200)
        x = min(max(event.x, NODE_R), w - NODE_R)
        y = min(max(event.y, NODE_R), h - NODE_R)
        self.vertices[v] = (x, y)
        self.redraw()

    def on_release(self, event):
        v = self.press_vertex
        self.press_vertex = None
        if v is None or self.dragged:
            return
        self.vertex_clicked(v)

    def on_double_click(self, event):
        """Double-click a vertex to delete it."""
        self.press_vertex = None
        self.dragged = False
        v = self.vertex_at(event.x, event.y)
        if v is not None:
            self.delete_vertex(v)
            self.redraw()

    def on_delete_key(self, event):
        """Delete / Backspace removes the currently selected (blue-outlined) vertex."""
        if self.selected in self.vertices:
            self.delete_vertex(self.selected)
            self.redraw()
        else:
            self.set_status("Click a vertex to select it first, then press Delete.")

    def undo_vertex(self):
        if not self.vertex_history:
            self.set_status("No vertices to undo.")
            return
        self.delete_vertex(self.vertex_history[-1])
        self.redraw()

    def on_right_click(self, event):
        v = self.vertex_at(event.x, event.y)
        if v is not None:
            self.delete_vertex(v)
            self.redraw()

    def vertex_clicked(self, v):
        if self.delete_mode.get():
            self.delete_vertex(v)
        elif self.selected is None:
            self.selected = v
            self.set_status(f"Source = {self.label(v)}. Now click the destination vertex.")
        elif self.selected == v:
            self.selected = None
            self.set_status("Selection cleared (self-loops are not supported).")
        else:
            u, self.selected = self.selected, None
            self.add_edge(u, v)
        self.redraw()

    # ------------------------------------------------------------- drawing
    def redraw(self):
        c = self.canvas
        c.delete("all")
        for (u, v), w in self.edges.items():
            self.draw_edge(u, v, w)

        # preview arrow from the selected source vertex to the mouse
        if self.selected in self.vertices and self.mouse_xy is not None:
            sx, sy = self.vertices[self.selected]
            mx, my = self.mouse_xy
            d = math.hypot(mx - sx, my - sy)
            if d > NODE_R:
                ux, uy = (mx - sx) / d, (my - sy) / d
                opts = {}
                if self.directed.get():
                    opts = {"arrow": tk.LAST, "arrowshape": (14, 16, 5)}
                c.create_line(sx + ux * NODE_R, sy + uy * NODE_R, mx, my,
                              fill=COL["selected"], width=2, dash=(6, 4), **opts)

        if not self.vertices:
            c.create_text(c.winfo_width() / 2, c.winfo_height() / 2,
                          text="1. Click here to add vertices\n"
                               "2. Click one vertex, then another to connect them\n"
                               "    (Directed = arrows, Weighted = optional weight per edge)\n"
                               "3. Drag vertices to move them\n"
                               "4. Double-click or right-click a vertex to delete it",
                          font=("Segoe UI", 13), fill="#90a4ae", justify="center")

        total = len(self.steps) if self.steps else max(len(self.visit_order), 1)
        index = {v: i for i, v in enumerate(self.visit_order)}

        # result banner (drawn under the vertices so they stay visible)
        if self.finished and self.visit_order:
            text = (f"✔ {self.algo_var.get()} complete:  "
                    + " → ".join(self.label(x) for x in self.visit_order))
            tid = c.create_text(20, 16, anchor="nw", text=text, fill="white",
                                font=("Segoe UI", 12, "bold"),
                                width=max(c.winfo_width() - 60, 200))
            x0, y0, x1, y1 = c.bbox(tid)
            box = c.create_rectangle(x0 - 12, y0 - 6, x1 + 12, y1 + 6,
                                     fill=COL["banner"], outline="")
            c.tag_lower(box, tid)

        # glowing dot travelling along the edge that led to the current vertex
        via = self.current_via
        if (self.current is not None and via and via[0] in self.vertices
                and via[1] in self.vertices):
            ax, ay = self.vertices[via[0]]
            bx, by = self.vertices[via[1]]
            dx, dy = ax + (bx - ax) * self.phase, ay + (by - ay) * self.phase
            c.create_oval(dx - 7, dy - 7, dx + 7, dy + 7, fill=COL["current"],
                          outline="white", width=2)

        for v, (x, y) in self.vertices.items():
            i = index.get(v)
            if v == self.current:
                fill = COL["current"]
            elif i is not None:
                fill = order_color(i, total)     # colour shows the visiting order
            else:
                fill = COL["node"]

            # soft drop shadow
            c.create_oval(x - NODE_R + 3, y - NODE_R + 4, x + NODE_R + 3, y + NODE_R + 4,
                          fill="#cfd8e3", outline="")

            # pulsing halo around the vertex being visited
            if v == self.current:
                pulse = 0.5 + 0.5 * math.sin(self.phase * 2 * math.pi)
                r1 = NODE_R + 5 + 6 * pulse
                r2 = NODE_R + 12 + 9 * pulse
                c.create_oval(x - r2, y - r2, x + r2, y + r2, width=2,
                              outline=blend(COL["current"], COL["bg"], 0.65 + 0.3 * (1 - pulse)))
                c.create_oval(x - r1, y - r1, x + r1, y + r1, width=3,
                              outline=blend(COL["current"], COL["bg"], 0.15 + 0.5 * (1 - pulse)))

            # ring for vertices involved in the current explanation step
            if v in self.rings:
                r = NODE_R + 7
                c.create_oval(x - r, y - r, x + r, y + r, outline=self.rings[v], width=4)

            # halo around the selected source vertex
            if v == self.selected:
                r = NODE_R + 6
                c.create_oval(x - r, y - r, x + r, y + r, outline="#90caf9", width=4)
                outline, width = COL["selected"], 4
            elif i is not None:
                outline, width = shade(fill, 0.7), 2
            else:
                outline, width = COL["node_outline"], 2

            c.create_oval(x - NODE_R, y - NODE_R, x + NODE_R, y + NODE_R,
                          fill=fill, outline=outline, width=width)
            size = 12 if len(self.label(v)) <= 2 else 9
            c.create_text(x, y, text=self.label(v), font=("Segoe UI", size, "bold"),
                          fill=COL["text"])

            # visiting-order badge
            if i is not None:
                bx, by = x + NODE_R * 0.78, y - NODE_R * 0.78
                c.create_oval(bx - 9, by - 9, bx + 9, by + 9, fill="#37474f",
                              outline="white", width=2)
                c.create_text(bx, by, text=str(i + 1), fill="white",
                              font=("Segoe UI", 8, "bold"))

        # completion effects: rainbow ripple through the visit order + confetti
        if self.celebrating:
            t = self.clock - self.celebrate_start
            for i, v in enumerate(self.visit_order):
                if v not in self.vertices:
                    continue
                local = t - i * 0.16
                if 0 <= local <= 0.9:
                    p = local / 0.9
                    x, y = self.vertices[v]
                    r = NODE_R + 4 + 36 * p
                    c.create_oval(x - r, y - r, x + r, y + r,
                                  outline=blend(order_color(i, total), COL["bg"], p),
                                  width=max(1, int(6 * (1 - p))))
            for p in self.confetti:
                c.create_rectangle(p["x"], p["y"], p["x"] + p["s"], p["y"] + p["s"] * 0.6,
                                   fill=p["color"], outline="")

    def draw_edge(self, u, v, w):
        x1, y1 = self.vertices[u]
        x2, y2 = self.vertices[v]
        d = math.hypot(x2 - x1, y2 - y1)
        if d < 1:
            return
        ux, uy = (x2 - x1) / d, (y2 - y1) / d
        px, py = -uy, ux
        directed = self.directed.get()   # directed -> arrows, undirected -> plain lines
        if not directed and (v, u) in self.edges and u > v:
            return  # same undirected line already drawn
        # for directed graphs, separate A->B and B->A so both arrows stay visible
        off = 8 if (directed and (v, u) in self.edges) else 0
        sx, sy = x1 + px * off + ux * NODE_R, y1 + py * off + uy * NODE_R
        ex, ey = x2 + px * off - ux * NODE_R, y2 + py * off - uy * NODE_R

        # tree edges take the colour of the vertex they discovered
        tree_target = None
        if (u, v) in self.tree_edges:
            tree_target = v
        elif not directed and (v, u) in self.tree_edges:
            tree_target = u
        color, width = COL["edge"], 2
        if tree_target is not None and tree_target in self.visit_order:
            total = len(self.steps) if self.steps else max(len(self.visit_order), 1)
            color = shade(order_color(self.visit_order.index(tree_target), total), 0.75)
            width = 4
        via = self.current_via
        if self.current is not None and via and (
                (u, v) == via or (not directed and (v, u) == via)):
            color, width = COL["current"], 5     # edge being traversed right now
        dash = None
        he = self.hl_edge
        if he and ((u, v) == he or (not directed and (v, u) == he)):
            if self.hl_kind == "skip":
                color, width, dash = KIND_STYLE["skip"][0], 4, (6, 4)
            elif self.hl_kind == "backtrack":
                color, width = KIND_STYLE["backtrack"][0], 4
        if directed:
            self.canvas.create_line(sx, sy, ex, ey, fill=color, width=width, dash=dash,
                                    arrow=tk.LAST, arrowshape=(14, 16, 5))
        else:
            self.canvas.create_line(sx, sy, ex, ey, fill=color, width=width, dash=dash)

        if self.weighted.get() and w is not None:
            side = off * 2.2 if off else 11
            mx = (sx + ex) / 2 + px * side
            my = (sy + ey) / 2 + py * side
            t = self.canvas.create_text(mx, my, text=fmt_w(w),
                                        font=("Segoe UI", 10, "bold"), fill=COL["weight_text"])
            x0, y0, x3, y3 = self.canvas.bbox(t)
            r = self.canvas.create_rectangle(x0 - 4, y0 - 1, x3 + 4, y3 + 1,
                                             fill=COL["weight_bg"],
                                             outline=COL["weight_border"])
            self.canvas.tag_raise(t, r)

    # ----------------------------------------------------------- animation
    def start_anim(self):
        """Run the ~25 fps animation loop (pulse, flowing dot, confetti)."""
        if self.anim_id is None:
            self.anim_id = self.root.after(40, self.anim_tick)

    def anim_tick(self):
        self.anim_id = None
        self.phase = (self.phase + 0.04) % 1.0
        self.clock += 0.04
        self.update_confetti()
        self.redraw()
        if self.current is not None or self.celebrating:
            self.start_anim()

    def start_celebration(self):
        w = max(self.canvas.winfo_width(), 300)
        h = max(self.canvas.winfo_height(), 300)
        self.confetti = [{
            "x": random.uniform(0, w), "y": random.uniform(-h * 0.6, 0),
            "vx": random.uniform(-1.2, 1.2), "vy": random.uniform(3, 7),
            "s": random.randint(6, 11), "color": random.choice(CONFETTI),
        } for _ in range(90)]
        self.celebrate_start = self.clock
        self.celebrating = True
        self.start_anim()

    def update_confetti(self):
        if not self.celebrating:
            return
        h = self.canvas.winfo_height()
        for p in self.confetti:
            p["x"] += p["vx"]
            p["y"] += p["vy"]
            p["vx"] += random.uniform(-0.15, 0.15)
        self.confetti = [p for p in self.confetti if p["y"] < h + 20]
        wave_end = len(self.visit_order) * 0.16 + 1.0
        if not self.confetti and self.clock - self.celebrate_start > wave_end:
            self.celebrating = False

    # ------------------------------------------------------------ traversal
    def refresh_start_choices(self):
        ids = sorted(self.vertices)
        labels = [self.label(i) for i in ids]
        self.label_to_id = {self.label(i): i for i in ids}
        self.start_box["values"] = labels
        if self.start_var.get() not in self.label_to_id:
            self.start_var.set(labels[0] if labels else "")

    def reset_traversal(self):
        if self.after_id is not None:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        self.auto = False
        self.auto_btn.config(text="Auto Play")
        self.steps = None
        self.step_index = 0
        self.visit_order = []
        self.tree_edges = set()
        self.current = None
        self.current_via = None
        self.finished = False
        self.celebrating = False
        self.confetti = []
        if self.anim_id is not None:
            self.root.after_cancel(self.anim_id)
            self.anim_id = None
        self.rings = {}
        self.hl_edge = None
        self.hl_kind = None
        self.output.set("Traversal order: –")
        self.log_intro()
        self.redraw()

    # ------------------------------------------------- step generation
    # The traversal is first simulated completely. Every action becomes one
    # "event" (a dict) with the text that is shown in the explanation panel.
    def make_event(self, kind, title, detail, ds, v=None, visit=False, via=None,
                   focus=None, edge=None):
        return {"kind": kind, "title": title, "detail": detail, "ds": ds, "v": v,
                "visit": visit, "via": via, "focus": focus, "edge": edge}

    def nbr_word(self):
        return "out-neighbor" if self.directed.get() else "neighbor"

    def edge_text(self, a, b):
        key = self.edge_key(a, b)
        w = self.edges.get(key) if key else None
        txt = f"{self.label(a)} {self.sep()} {self.label(b)}"
        if self.weighted.get() and w is not None:
            txt += f", weight {fmt_w(w)}"
        return txt

    def names(self, items):
        return "[" + ", ".join(self.label(x) for x in items) + "]"

    def visits_so_far(self, steps):
        return sum(1 for e in steps if e["visit"])

    def bfs(self, root, seen, steps, new_component):
        L, nw = self.label, self.nbr_word()
        seen.add(root)
        q = deque([root])
        k = self.visits_so_far(steps) + 1
        if new_component:
            title = f"New component: start at {L(root)}"
            detail = (f"The earlier vertices are finished, but {L(root)} was never reached. "
                      f"Start a new BFS from it: mark it visited (visit #{k}) and put it "
                      "in the queue.")
        else:
            title = f"Start at {L(root)}"
            detail = (f"BFS begins at the start vertex {L(root)}. Mark it visited "
                      f"(visit #{k}) and put it in the queue.")
        steps.append(self.make_event("visit", title, detail, f"Queue: {self.names(q)}",
                                     v=root, visit=True))
        while q:
            u = q.popleft()
            nbrs = self.neighbors(u)
            if nbrs:
                detail = (f"Remove {L(u)} from the front of the queue and look at its "
                          f"{nw}s in order: {', '.join(L(x) for x in nbrs)}.")
            else:
                detail = (f"Remove {L(u)} from the front of the queue. It has no {nw}s, "
                          "so there is nothing to explore from it.")
            steps.append(self.make_event("process", f"Process {L(u)}", detail,
                                         f"Queue: {self.names(q)}", v=u, focus=u))
            for w in nbrs:
                if w not in seen:
                    seen.add(w)
                    q.append(w)
                    k += 1
                    detail = (f"{L(w)} is a {nw} of {L(u)} (edge {self.edge_text(u, w)}) and "
                              f"has not been visited. Mark it visited (visit #{k}) and add "
                              "it to the back of the queue.")
                    steps.append(self.make_event("visit", f"Visit {L(w)}", detail,
                                                 f"Queue: {self.names(q)}", v=w, visit=True,
                                                 via=(u, w), focus=u))
                else:
                    detail = (f"{L(w)} is a {nw} of {L(u)}, but it was already visited, so "
                              "ignore it. (This is what stops BFS from looping forever.)")
                    steps.append(self.make_event("skip", f"Skip {L(w)}", detail,
                                                 f"Queue: {self.names(q)}", v=w, focus=u,
                                                 edge=(u, w)))

    def dfs(self, root, seen, steps, new_component):
        L, nw = self.label, self.nbr_word()
        stack = []
        k = self.visits_so_far(steps)

        def go(u, parent, via):
            nonlocal k
            seen.add(u)
            stack.append(u)
            k += 1
            if parent is None:
                if new_component:
                    title = f"New component: start at {L(u)}"
                    detail = (f"The earlier vertices are finished, but {L(u)} was never "
                              f"reached. Start a new DFS from it: mark it visited "
                              f"(visit #{k}) and push it on the stack.")
                else:
                    title = f"Start at {L(u)}"
                    detail = (f"DFS begins at the start vertex {L(u)}. Mark it visited "
                              f"(visit #{k}) and push it on the stack.")
            else:
                title = f"Visit {L(u)}"
                detail = (f"Go deeper: {L(u)} is an unvisited {nw} of {L(parent)} "
                          f"(edge {self.edge_text(parent, u)}). Mark it visited "
                          f"(visit #{k}) and push it on the stack.")
            steps.append(self.make_event("visit", title, detail,
                                         f"Stack: {self.names(stack)}", v=u, visit=True,
                                         via=via, focus=parent))
            for w in self.neighbors(u):
                if w in seen:
                    detail = (f"At {L(u)}: the {nw} {L(w)} was already visited, so skip it.")
                    steps.append(self.make_event("skip", f"Skip {L(w)}", detail,
                                                 f"Stack: {self.names(stack)}", v=w,
                                                 focus=u, edge=(u, w)))
                else:
                    go(w, u, (u, w))
            stack.pop()
            if parent is not None:
                detail = (f"{L(u)} has no more unvisited {nw}s. Pop it from the stack and "
                          f"backtrack to {L(parent)} to try its next {nw}.")
                steps.append(self.make_event("backtrack", f"Backtrack from {L(u)}", detail,
                                             f"Stack: {self.names(stack)}", v=u,
                                             focus=parent, edge=(parent, u)))
            else:
                detail = (f"{L(u)} has no more unvisited {nw}s and the stack is empty, "
                          "so this DFS is finished.")
                steps.append(self.make_event("backtrack", f"Finish at {L(u)}", detail,
                                             f"Stack: {self.names(stack)}", v=u))

        go(root, None, None)

    def build_steps(self):
        if not self.vertices:
            messagebox.showinfo("No graph", "Add some vertices first.")
            return False
        start = self.label_to_id.get(self.start_var.get(), min(self.vertices))
        order = [start]
        if self.all_components.get():
            order += [v for v in sorted(self.vertices) if v != start]
        algo = self.algo_var.get()
        seen, steps = set(), []
        first = True
        for r in order:
            if r in seen:
                continue
            if algo == "BFS":
                self.bfs(r, seen, steps, not first)
            else:
                self.dfs(r, seen, steps, not first)
            first = False

        visit_order = [e["v"] for e in steps if e["visit"]]
        detail = (f"{'The queue' if algo == 'BFS' else 'The stack'} is empty, so "
                  f"{algo} is finished.\nVisit order: "
                  + " → ".join(self.label(x) for x in visit_order)
                  + "\nTime complexity: O(V + E).")
        unreached = [v for v in sorted(self.vertices) if v not in seen]
        if unreached:
            detail += (f"\nNot reachable from the start vertex: "
                       f"{', '.join(self.label(x) for x in unreached)} "
                       "(tick 'Visit all components' to include them).")
        steps.append(self.make_event("done", "Traversal complete", detail,
                                     "Queue: [ ]" if algo == "BFS" else "Stack: [ ]"))
        self.steps = steps
        self.step_index = 0
        return True

    def step(self):
        """Perform one step. Returns False when nothing is left to do."""
        if self.steps is None and not self.build_steps():
            return False
        if self.step_index >= len(self.steps):
            self.set_status("Traversal already complete. Press Reset to run again.")
            return False

        e = self.steps[self.step_index]
        self.step_index += 1
        total = len(self.steps)
        name = self.algo_var.get()

        # what the graph shows for this step
        rings = {}
        if e["focus"] is not None:
            rings[e["focus"]] = RING_FOCUS
        if e["kind"] == "skip":
            rings[e["v"]] = KIND_STYLE["skip"][0]
        elif e["kind"] == "backtrack":
            rings[e["v"]] = KIND_STYLE["backtrack"][0]
        self.rings = rings
        self.hl_edge = e["edge"]
        self.hl_kind = e["kind"]
        if e["visit"]:
            self.visit_order.append(e["v"])
            self.current = e["v"]
            self.current_via = e["via"]
            if e["via"] is not None:
                self.tree_edges.add(e["via"])
        else:
            self.current = None
            self.current_via = None

        if self.visit_order:
            text = " → ".join(self.label(x) for x in self.visit_order)
            self.output.set(f"{name} order: {text}")

        # explanation goes to the side panel, never over the graph
        self.log_add(self.step_index, total, e)
        self.set_status(f"Step {self.step_index}/{total}: {e['title']}")

        if e["kind"] == "done":
            self.current = None
            self.current_via = None
            self.rings = {}
            self.hl_edge = None
            self.finished = True
            self.set_status(f"{name} complete - {len(self.visit_order)} vertices visited.")
            self.start_celebration()
        elif self.current is not None:
            self.start_anim()
        self.redraw()
        return self.step_index < total

    def toggle_auto(self):
        if self.auto:
            self.auto = False
            self.auto_btn.config(text="Auto Play")
            if self.after_id is not None:
                self.root.after_cancel(self.after_id)
                self.after_id = None
            return
        if self.steps is not None and self.step_index >= len(self.steps):
            self.reset_traversal()
        self.auto = True
        self.auto_btn.config(text="Pause")
        self.auto_tick()

    def auto_tick(self):
        if not self.auto:
            return
        more = self.step()
        if not more:
            self.auto = False
            self.auto_btn.config(text="Auto Play")
            self.after_id = None
            return
        delay = int(1600 / self.speed.get())  # speed 1..10 -> 1600ms..160ms
        self.after_id = self.root.after(delay, self.auto_tick)


if __name__ == "__main__":
    root = tk.Tk()
    GraphVisualizer(root)
    root.mainloop()
