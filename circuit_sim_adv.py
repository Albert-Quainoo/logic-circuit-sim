from circuit import Wire, AND, OR, NOT
import re
import html
import itertools
import ast
import sys
import math
from io import StringIO


try:
    import matplotlib.pyplot as plt
    HAS_MPL = True
except ImportError:
    HAS_MPL = False

try:
    from PyQt6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout,
                                  QHBoxLayout, QLabel, QLineEdit, QPushButton,
                                  QTextEdit, QTableWidget, QTableWidgetItem, QTabWidget,
                                  QCheckBox, QHeaderView, QLineEdit, QMessageBox,
                                  QScrollArea)
    from PyQt6.QtCore import Qt, QTimer, QPointF, QRectF
    from PyQt6.QtGui import (
        QGuiApplication, QTextCursor, QTextCharFormat, QColor,
        QShortcut, QKeySequence, QPixmap, QPainter, QPen, QBrush, QPainterPath
    )
    HAS_PYQT = True
except ImportError:
    HAS_PYQT = False

class Gate:
    def __init__(self, gate_type, inputs, output):
        self.gate_type = gate_type
        self.input = inputs
        self.output = output

def extract_vars(expr):
    """Return sorted list of variable names appearing in the expression."""
    return sorted(set(re.findall(r"[A-Za-z]", expr)))

def to_python_expr(expr):
    """
    Convert user-level logical syntax to Python bitwise syntax for AST parsing.
    
    !  -> ~  (Bitwise NOT)
    *  -> &  (Bitwise AND)
    +  -> |  (Bitwise OR)
    ^  -> ^  (Bitwise XOR)
    %  -> %  (Modulo) -> Mapped to NAND
    ~  -> << (LShift) -> Mapped to NOR
    #  -> >> (RShift) -> Mapped to XNOR
    """
    e = expr
    # Replace ~ (NOR) first so it doesn't conflict with ! -> ~ (NOT)
    e = e.replace("~", " << ")
    e = e.replace("!", " ~ ")
    e = e.replace("*", " & ")
    e = e.replace("+", " | ")
    e = e.replace("^", " ^ ")
    e = e.replace("%", " % ")
    e = e.replace("#", " >> ")

    return " ".join(e.split())

def xor_gate(w1, w2):
    out1 = Wire()
    out2 = Wire()
    out3 = Wire()
    out = Wire()
    OR(w1, w2, out1)
    AND(w1, w2, out2)
    NOT(out2, out3)
    AND(out1, out3, out)
    return out

def nand_gate(w1, w2):
    temp = Wire()
    out = Wire()
    AND(w1, w2, temp)
    NOT(temp, out)
    return out

def nor_gate(w1, w2):
    temp = Wire()
    out = Wire()
    OR(w1, w2, temp)
    NOT(temp, out)
    return out

def xnor_gate(w1, w2):
    xor_out = xor_gate(w1, w2)
    out = Wire()
    NOT(xor_out, out)
    return out


def build_circuit_ast(expr_str, wire_map, trace=False):
    """
    Build the circuit from the expression AST.

    If trace=True, print a step-by-step log of the traversal and gate creation.
    """

    expr_ast = ast.parse(to_python_expr(expr_str), mode="eval")
    gate_list = []
    gate_counter = {"count": 0}


    def walk(node):
        if isinstance(node, ast.Name):
            return node.id, wire_map[node.id]

        # Handle NOT (! -> ~)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Invert):
            input_name, in_wire = walk(node.operand)
            out_wire = Wire()
            gate_counter["count"] += 1
            gate_name = f"W{gate_counter['count']}"
            if trace:
                gate_list.append(f"{gate_name} = NOT({input_name})")
            NOT(in_wire, out_wire)
            return gate_name, out_wire

        # Handle Binary Operations
        if isinstance(node, ast.BinOp):
            left_name, left_wire = walk(node.left)
            right_name, right_wire = walk(node.right)

            out_wire = Wire()
            gate_counter["count"] += 1
            gate_name = f"W{gate_counter['count']}"

            if isinstance(node.op, ast.BitAnd):  # * -> &
                AND(left_wire, right_wire, out_wire)
                if trace:
                    gate_list.append(f"{gate_name} = {left_name} AND {right_name}")
            elif isinstance(node.op, ast.BitOr):  # + -> |
                OR(left_wire, right_wire, out_wire)
                if trace:
                    gate_list.append(f"{gate_name} = {left_name} OR {right_name}")
            elif isinstance(node.op, ast.BitXor): # ^ -> ^
                out_wire = xor_gate(left_wire, right_wire)
                if trace:
                    gate_list.append(f"{gate_name} = {left_name} XOR {right_name}")
            elif isinstance(node.op, ast.Mod):    # % -> % (NAND)
                out_wire = nand_gate(left_wire, right_wire)
                if trace:
                    gate_list.append(f"{gate_name} = {left_name} NAND {right_name}")
            elif isinstance(node.op, ast.LShift): # ~ -> << (NOR)
                out_wire = nor_gate(left_wire, right_wire)
                if trace:
                    gate_list.append(f"{gate_name} = {left_name} NOR {right_name}")
            elif isinstance(node.op, ast.RShift): # # -> >> (XNOR)
                out_wire = xnor_gate(left_wire, right_wire)
                if trace:
                    gate_list.append(f"{gate_name} = {left_name} XNOR {right_name}")
            else:
                raise ValueError(f"Unsupported operation: {type(node.op)}")

            return gate_name, out_wire

        if isinstance(node, ast.Call):
            fname = node.func.id.upper()
            args_data = [walk(arg) for arg in node.args]
            arg_names = [name for name, _ in args_data]
            arg_wires = [wire for _, wire in args_data]

            if fname == "XOR":
                out_wire = xor_gate(*arg_wires)
            elif fname == "NAND":
                out_wire = nand_gate(*arg_wires)
            elif fname == "NOR":
                out_wire = nor_gate(*arg_wires)
            elif fname == "XNOR":
                out_wire = xnor_gate(*arg_wires)
            else:
                raise ValueError(f"Unsupported function: {fname}")

            gate_counter["count"] += 1
            gate_name = f"W{gate_counter['count']}"
            if trace:
                gate_list.append(f"{gate_name} = {fname}({', '.join(arg_names)})")
            return gate_name, out_wire

        raise ValueError(f"Unsupported expression node: {type(node)}")

    if trace:
        print(f"\n┌─ Circuit Build: {expr_str}")

    final_name, out_wire = walk(expr_ast.body)

    if trace:
        print("│")
        for gate in gate_list:
            print(f"│  {gate}")
        print("│")
        print(f"└─ Output: {final_name} ({len(gate_list)} gates)\n")

    return out_wire


def get_truth_table(expr):
    """
    Build the circuit for expr and return:
    - input_order: list of variable names
    - rows: list of dictionaries like {'A':0, 'B':1, ..., 'Output':1}
    """
    input_order = extract_vars(expr)
    wire_map = {name: Wire() for name in input_order}
    # Trace disabled during normal truth table generation
    output_wire = build_circuit_ast(expr, wire_map, trace=False)

    rows = []
    for bits in itertools.product([False, True], repeat=len(input_order)):
        # assign each input for this combination
        for name, val in zip(input_order, bits):
            wire_map[name].reset()
            wire_map[name].value = val

        row = {name: int(val) for name, val in zip(input_order, bits)}
        row["Output"] = int(output_wire.value)
        rows.append(row)

    return input_order, rows



def evaluate(expr):
    input_order, rows = get_truth_table(expr)

    print("\nTruth Table for:", expr)
    print(" ".join(input_order), "| Output")
    print("-" * (len(input_order) * 2 + 10))

    for row in rows:
        bits = [str(row[v]) for v in input_order]
        print(" ".join(bits), "|   ", row["Output"])



#---- Visualisation ----#
def visualize_ast_build(expr):
    """
    One-time visualisation: show how the AST is walked and gates are created.
    """
    input_order = extract_vars(expr)
    wire_map = {name: Wire() for name in input_order}

    # Setting trace to True will print traversal + gate creation
    build_circuit_ast(expr, wire_map, trace=True)


def plot_truth_table(expr):
    """
    Show the truth table as a matplotlib table (good for screenshots in the report).
    """
    if not HAS_MPL:
        print("Matplotlib not available: skipping truth table plot.")
        return

    input_order, rows = get_truth_table(expr)
    col_labels = input_order + ["Output"]
    cell_data = [[row[var] for var in col_labels] for row in rows]

    _fig, ax = plt.subplots()
    ax.axis("off")

    table = ax.table(
        cellText=cell_data,
        colLabels=col_labels,
        loc="center"
    )

    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1, 1.5)

    ax.set_title(f"Truth Table for: {expr}")
    plt.tight_layout()
    plt.show()


def step_simulation(expr):
    input_order, rows = get_truth_table(expr)

    print("\nStep-through simulation for:", expr)
    print("Order of inputs:", ", ".join(input_order))
    print("-" * 40)

    for i, row in enumerate(rows, start=1):
        inputs_str = ", ".join(f"{name}={row[name]}" for name in input_order)
        print(f"Step {i}: {inputs_str} -> Output={row['Output']}")

def plot_output_distribution(expr):
    if not HAS_MPL:
        print("Matplotlib not available: skipping output distribution plot.")
        return

    _, rows = get_truth_table(expr)
    zeros = sum(1 for r in rows if r["Output"] == 0)
    ones = sum(1 for r in rows if r["Output"] == 1)

    _fig, ax = plt.subplots()
    ax.bar(["0", "1"], [zeros, ones])
    ax.set_xlabel("Output value")
    ax.set_ylabel("Number of input combinations")
    ax.set_title(f"Output distribution for: {expr}")
    plt.tight_layout()
    plt.show()



class CircuitSimGUI(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Logic Circuit Workbench")
        self.setGeometry(100, 100, 1100, 750)

        main_widget = QWidget()
        self.setCentralWidget(main_widget)
        main_layout = QVBoxLayout(main_widget)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("QScrollArea { border: none; }")
        main_layout.addWidget(scroll)

        # All content sits inside a scroll area so it never overflows the window height.
        content = QWidget()
        scroll.setWidget(content)
        layout = QVBoxLayout(content)
        layout.setSpacing(14)
        layout.setContentsMargins(24, 24, 24, 24)

        self.setStyleSheet("""
            QMainWindow {
                background: qlineargradient(x1:0, y1:0, x2:1, y2:1,
                                            stop:0 #0b1220, stop:1 #111827);
                color: #e5e7eb;
                font-family: 'Segoe UI', 'Helvetica Neue', Arial;
            }
            QLabel { font-size: 13px; color: #e5e7eb; }
            QLabel#title { font-size: 24px; font-weight: 800; letter-spacing: 0.4px; }
            QLabel#subtitle { color: #cbd5e1; }
            QLabel#tag {
                background: #111827;
                color: #cbd5e1;
                padding: 6px 10px;
                border-radius: 10px;
                border: 1px solid #1f2937;
                font-weight: 600;
            }
            QLineEdit {
                padding: 12px 14px;
                font-size: 15px;
                border: 1px solid #1f2937;
                border-radius: 12px;
                background-color: #0f172a;
                color: #e2e8f0;
                selection-background-color: #38bdf8;
                selection-color: #0b1220;
            }
            QLineEdit:focus {
                border: 1px solid #38bdf8;
                background-color: #0e1a2e;
            }
            QPushButton {
                padding: 12px 18px;
                font-size: 14px;
                font-weight: 700;
                background: qlineargradient(x1:0, y1:0, x2:1, y2:1,
                                            stop:0 #0ea5e9, stop:1 #22d3ee);
                color: #0b1220;
                border: none;
                border-radius: 12px;
            }
            QPushButton:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:1,
                                            stop:0 #38bdf8, stop:1 #7dd3fc); }
            QPushButton:pressed { background: #0284c7; color: white; }
            QPushButton:disabled {
                background-color: #1f2937;
                color: #94a3b8;
            }
            QPushButton#ghost { 
                background: #111827; 
                color: #cbd5e1; 
                border: 1px solid #1f2937; 
                padding: 10px 14px; 
                border-radius: 12px; 
            } 
            QPushButton#ghost:hover { border-color: #38bdf8; color: #38bdf8; } 
            QPushButton#pill {
                background: #0f172a;
                border: 1px solid #1f2937;
                color: #cbd5e1;
                padding: 8px 12px;
                border-radius: 14px;
                font-weight: 700;
            }
            QPushButton#pill:hover { border-color: #38bdf8; color: #38bdf8; }
            QPushButton#primary {
                min-height: 38px;
                padding: 12px 20px;
                font-size: 14px;
                font-weight: 800;
                background: qlineargradient(x1:0, y1:0, x2:1, y2:1,
                                            stop:0 #22d3ee, stop:1 #0ea5e9);
                color: #0b1220;
                border: 1px solid #0ea5e9;
                border-radius: 12px;
            }
            QPushButton#primary:hover {
                background: qlineargradient(x1:0, y1:0, x2:1, y2:1,
                                            stop:0 #7dd3fc, stop:1 #38bdf8);
            }
            QPushButton#primary:pressed {
                background: #0284c7;
                color: white;
            }
            QScrollArea QWidget { background: transparent; }
            QTableWidget {
                background-color: #0f172a;
                border: 1px solid #1f2937;
                border-radius: 12px;
                font-size: 13px;
                gridline-color: #1f2937;
                color: #e2e8f0;
                selection-background-color: #1d4ed8;
                selection-color: #e2e8f0;
            }
            QHeaderView::section {
                background: #111827;
                color: #cbd5e1;
                border: none;
                padding: 10px 6px;
                font-weight: 700;
            }
            QTextEdit {
                background-color: #0f172a;
                border: 1px solid #1f2937;
                border-radius: 12px;
                font-family: 'JetBrains Mono', 'Fira Code', 'Consolas', 'Courier New', monospace;
                font-size: 13px;
                padding: 12px;
                color: #e2e8f0;
                selection-background-color: #0ea5e9;
                selection-color: #0b1220;
            }
            QTabWidget::pane {
                border: 1px solid #1f2937;
                border-radius: 14px;
                background: #0c1220;
            }
            QTabBar::tab {
                padding: 10px 16px;
                background-color: #0f172a;
                color: #cbd5e1;
                border: 1px solid #1f2937;
                border-bottom: none;
                border-top-left-radius: 12px;
                border-top-right-radius: 12px;
                margin-right: 8px;
            }
            QTabBar::tab:selected {
                background-color: #0ea5e9;
                color: #0b1220;
                font-weight: 800;
                border-color: #0ea5e9;
            }
            QTabBar::tab:hover { background: #111827; }
            QWidget#card {
                background: #0c1220;
                border: 1px solid #1f2937;
                border-radius: 16px;
            }
            QLabel#badge {
                padding: 6px 10px;
                border-radius: 10px;
                font-weight: 700;
                color: #0b1220;
                background: #38bdf8;
            }
            QLabel#sandboxTitle { font-weight: 700; color: #cbd5e1; }
            QLabel#message { border-radius: 12px; padding: 12px; }
            QCheckBox { color: #cbd5e1; font-weight: 600; }
            QCheckBox::indicator {
                width: 18px; height: 18px;
                border: 1px solid #1f2937;
                border-radius: 6px;
                background: #0f172a;
            }
            QCheckBox::indicator:checked {
                background: #0ea5e9;
                border-color: #0ea5e9;
            }
        """)

        title_label = QLabel("Digital Logic Circuit Workbench")
        title_label.setObjectName("title")
        layout.addWidget(title_label)

        subtitle = QLabel("Analyze boolean expressions with live truth tables, circuit steps, and simulation output.")
        subtitle.setObjectName("subtitle")
        subtitle.setWordWrap(True)
        layout.addWidget(subtitle)

        shell = QWidget()
        shell.setObjectName("card")
        shell_layout = QVBoxLayout(shell)
        shell_layout.setSpacing(14)
        shell_layout.setContentsMargins(18, 18, 18, 18)
        layout.addWidget(shell)

        expr_label = QLabel("Boolean Expression")
        shell_layout.addWidget(expr_label)

        input_row = QHBoxLayout()
        self.input_field = QLineEdit()
        self.input_field.setPlaceholderText("Type an expression. Example: (A+B)*!C  |  A^B  |  (A+B)#C  |  !A + (B*C)")
        self.input_field.returnPressed.connect(self.on_evaluate_clicked)
        input_row.addWidget(self.input_field)
        shell_layout.addLayout(input_row)

        samples_row = QHBoxLayout()
        sample_exprs = [
            "(A+B)*!C",
            "A^B",
            "A%B",
            "(A+B)#C",
            "!A + (B*C)"
        ]
        for expr_sample in sample_exprs:
            btn = QPushButton(expr_sample)
            btn.setObjectName("pill")
            btn.clicked.connect(lambda _=False, val=expr_sample: self.apply_sample(val))
            samples_row.addWidget(btn)
        samples_row.addStretch()
        shell_layout.addLayout(samples_row)

        controls_row = QHBoxLayout()
        self.live_toggle = QCheckBox("Live evaluate as you type")
        self.live_toggle.setChecked(True)
        controls_row.addWidget(self.live_toggle)

        controls_row.addStretch()

        self.clear_btn = QPushButton("Reset")
        self.clear_btn.setObjectName("ghost")
        self.clear_btn.clicked.connect(self.reset_ui)
        controls_row.addWidget(self.clear_btn)

        self.evaluate_btn = QPushButton("Evaluate now")
        self.evaluate_btn.setObjectName("primary")
        self.evaluate_btn.setMinimumWidth(140)
        self.evaluate_btn.clicked.connect(self.on_evaluate_clicked)
        controls_row.addWidget(self.evaluate_btn)

        shell_layout.addLayout(controls_row)

        tag_row = QHBoxLayout()
        for tag in ["! NOT", "* AND", "+ OR", "^ XOR", "% NAND", "~ NOR", "# XNOR"]:
            pill = QLabel(tag)
            pill.setObjectName("tag")
            tag_row.addWidget(pill)
        tag_row.addStretch()
        shell_layout.addLayout(tag_row)

        helper_text = QLabel(
            "Tip: ! is NOT, * is AND, + is OR, ^ is XOR, % is NAND, ~ is NOR, # is XNOR. Wrap groups like (A+B)*!C. "
            "Use the Sandbox toggles below to flip inputs without retyping."
        )
        helper_text.setStyleSheet("color: #94a3b8; font-size: 12px;")
        helper_text.setWordWrap(True)
        shell_layout.addWidget(helper_text)

        self.message_label = QLabel()
        self.message_label.setObjectName("message")
        self.message_label.setWordWrap(True)
        shell_layout.addWidget(self.message_label)

        sandbox_card = QWidget()
        sandbox_card.setObjectName("card")
        sandbox_layout = QVBoxLayout(sandbox_card)
        sandbox_layout.setSpacing(10)
        sandbox_layout.setContentsMargins(14, 14, 14, 14)
        sandbox_header = QHBoxLayout()
        sandbox_title = QLabel("Sandbox: toggle inputs and see output")
        sandbox_title.setObjectName("sandboxTitle")
        sandbox_header.addWidget(sandbox_title)
        sandbox_header.addStretch()
        self.sandbox_output_label = QLabel("Output: —")
        self.sandbox_output_label.setObjectName("badge")
        sandbox_header.addWidget(self.sandbox_output_label)
        sandbox_layout.addLayout(sandbox_header)
        self.sandbox_toggle_row = QHBoxLayout()
        self.sandbox_toggle_row.setSpacing(10)
        self.sandbox_toggle_row.setContentsMargins(0, 0, 0, 0)
        self.sandbox_toggle_row.addWidget(QLabel("Evaluate an expression to enable toggles."))
        self.sandbox_toggle_row.addStretch()
        sandbox_layout.addLayout(self.sandbox_toggle_row)
        shell_layout.addWidget(sandbox_card)

        diagram_card = QWidget()
        diagram_card.setObjectName("card")
        diagram_layout = QVBoxLayout(diagram_card)
        diagram_layout.setSpacing(8)
        diagram_layout.setContentsMargins(14, 14, 14, 14)
        diagram_header = QHBoxLayout()
        diagram_title = QLabel("Gate Preview")
        diagram_title.setObjectName("sandboxTitle")
        diagram_header.addWidget(diagram_title)
        diagram_header.addStretch()
        diagram_hint = QLabel("Auto-updates with evaluate (debounced).")
        diagram_hint.setStyleSheet("color:#94a3b8; font-size:12px;")
        diagram_header.addWidget(diagram_hint)
        diagram_layout.addLayout(diagram_header)
        self.diagram_label = QLabel("Evaluate to see a simple gate diagram.")
        self.diagram_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.diagram_label.setMinimumHeight(280)
        diagram_layout.addWidget(self.diagram_label)
        shell_layout.addWidget(diagram_card)

        self.tabs = QTabWidget()
        shell_layout.addWidget(self.tabs)

        self.truth_table = QTableWidget()
        self.truth_table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.truth_table.verticalHeader().setVisible(False)
        self.truth_table.setAlternatingRowColors(True)
        self.truth_table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        self.truth_table.cellClicked.connect(self.on_truth_row_clicked)
        self.truth_table.setSortingEnabled(True)
        self.truth_table.horizontalHeader().sectionClicked.connect(self.on_header_clicked)
        self.tabs.addTab(self.truth_table, "Truth Table")

        build_tab = QWidget()
        build_layout = QVBoxLayout(build_tab)
        build_layout.setSpacing(8)
        build_layout.setContentsMargins(10, 10, 10, 10)
        controls_build = QHBoxLayout()
        self.build_search = QLineEdit()
        self.build_search.setPlaceholderText("Search build steps")
        find_build = QPushButton("Find")
        find_build.clicked.connect(lambda: self.highlight_text(self.ast_output, self.build_search.text()))
        clear_build = QPushButton("Clear")
        clear_build.setObjectName("ghost")
        clear_build.clicked.connect(lambda: self.clear_highlight(self.ast_output, self.build_search))
        copy_build = QPushButton("Copy")
        copy_build.setObjectName("ghost")
        copy_build.clicked.connect(lambda: self.copy_text(self.ast_output.toPlainText()))
        refresh_build = QPushButton("Refresh")
        refresh_build.clicked.connect(self.show_ast_walk)
        controls_build.addWidget(self.build_search)
        controls_build.addWidget(find_build)
        controls_build.addWidget(clear_build)
        controls_build.addWidget(copy_build)
        controls_build.addWidget(refresh_build)
        controls_build.addStretch()
        build_layout.addLayout(controls_build)
        self.ast_output = QTextEdit()
        self.ast_output.setReadOnly(True)
        self.ast_output.setPlainText("Circuit build steps will appear here after you evaluate an expression.")
        build_layout.addWidget(self.ast_output)
        self.tabs.addTab(build_tab, "Gate Build")

        sim_tab = QWidget()
        sim_layout = QVBoxLayout(sim_tab)
        sim_layout.setSpacing(8)
        sim_layout.setContentsMargins(10, 10, 10, 10)
        controls_sim = QHBoxLayout()
        self.sim_search = QLineEdit()
        self.sim_search.setPlaceholderText("Search simulation rows")
        find_sim = QPushButton("Find")
        find_sim.clicked.connect(lambda: self.highlight_text(self.step_output, self.sim_search.text()))
        clear_sim = QPushButton("Clear")
        clear_sim.setObjectName("ghost")
        clear_sim.clicked.connect(lambda: self.clear_highlight(self.step_output, self.sim_search))
        copy_sim = QPushButton("Copy")
        copy_sim.setObjectName("ghost")
        copy_sim.clicked.connect(lambda: self.copy_text(self.step_output.toPlainText()))
        refresh_sim = QPushButton("Refresh")
        refresh_sim.clicked.connect(self.on_evaluate_clicked)
        controls_sim.addWidget(self.sim_search)
        controls_sim.addWidget(find_sim)
        controls_sim.addWidget(clear_sim)
        controls_sim.addWidget(copy_sim)
        controls_sim.addWidget(refresh_sim)
        controls_sim.addStretch()
        sim_layout.addLayout(controls_sim)
        self.step_output = QTextEdit()
        self.step_output.setReadOnly(True)
        self.step_output.setPlainText("Step-through simulation results will be listed here.")
        sim_layout.addWidget(self.step_output)
        self.step_panel = sim_tab
        self.step_tab_index = self.tabs.addTab(sim_tab, "Step Simulation")
        self.tabs.setTabVisible(self.step_tab_index, False)

        self.current_expr = None
        self.last_input_order = []
        self.last_rows = []
        self.sandbox_toggles = {}
        self.combo_map = {}
        self.output_sort_desc = False
        self.live_timer = QTimer(self)
        self.live_timer.setSingleShot(True)
        self.live_timer.setInterval(450)
        self.live_timer.timeout.connect(lambda: self.evaluate_expression(from_live=True))

        self.input_field.textChanged.connect(self.on_expr_changed)
        self.live_toggle.stateChanged.connect(self.on_expr_changed)
        self.register_shortcuts()
        self.show_message("Enter an expression and press Evaluate to begin.")
        layout.addStretch(1)

    def apply_sample(self, expr):
        self.input_field.setText(expr)
        self.on_evaluate_clicked()

    def on_expr_changed(self):
        # Debounce live evaluation so we don't recompute on every keystroke.
        if self.live_toggle.isChecked():
            expr = self.input_field.text().strip()
            if expr:
                self.live_timer.start()
            else:
                self.reset_ui(clear_message=False)
        else:
            self.live_timer.stop()

    def on_evaluate_clicked(self):
        self.evaluate_expression(from_live=False)

    def evaluate_expression(self, from_live=False):
        expr = self.input_field.text().strip()
        if not expr:
            self.show_message("Please enter a boolean expression to evaluate.", "warning")
            return

        try:
            self.current_expr = expr
            input_order, rows = get_truth_table(expr)
            self.last_input_order = input_order
            self.last_rows = rows
            self.combo_map = {tuple(row[name] for name in input_order): row["Output"] for row in rows}

            self.truth_table.clear()
            col_labels = input_order + ["Output"]
            self.truth_table.setColumnCount(len(col_labels))
            self.truth_table.setRowCount(len(rows))
            self.truth_table.setHorizontalHeaderLabels(col_labels)
            self.set_header_tooltips(col_labels)

            for i, row in enumerate(rows):
                for j, label in enumerate(col_labels):
                    item = QTableWidgetItem(str(row[label]))
                    item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                    self.truth_table.setItem(i, j, item)

            self.populate_step_simulation(expr, input_order, rows)
            self.show_ast_walk()
            self.rebuild_sandbox_toggles(input_order)
            self.update_sandbox_output()
            self.update_gate_diagram(expr)

            summary = f"{'Live' if from_live else 'Evaluated'} '{expr}' using {len(input_order)} variable(s) and {len(rows)} combinations."
            self.show_message(summary, "success" if not from_live else "info")

        except Exception as e:
            self.truth_table.clear()
            self.truth_table.setRowCount(1)
            self.truth_table.setColumnCount(1)
            self.truth_table.setItem(0, 0, QTableWidgetItem(f"Error: {str(e)}"))
            hint = "Hint: use ! for NOT, * for AND, + for OR, ^ for XOR, % for NAND, ~ for NOR, # for XNOR. Wrap groups like (A+B)*!C."
            self.show_message(f"Unable to evaluate expression: {e}\n{hint}", "error")
            self.diagram_label.setText("Diagram unavailable due to error.")

    def reset_ui(self, clear_message=True):
        self.current_expr = None
        self.last_input_order = []
        self.last_rows = []
        self.combo_map = {}
        self.rebuild_sandbox_toggles([])
        self.truth_table.clear()
        self.truth_table.setRowCount(0)
        self.truth_table.setColumnCount(0)
        self.ast_output.setPlainText("Circuit build steps will appear here after you evaluate an expression.")
        self.step_output.setPlainText("Step-through simulation results will be listed here.")
        if clear_message:
            self.show_message("Cleared. Enter a new expression to evaluate.", "info")
        if hasattr(self, "step_tab_index"):
            # Hide the step tab until a row click explicitly asks for it.
            self.tabs.setTabVisible(self.step_tab_index, False)
            self.tabs.setCurrentIndex(0)

    def show_message(self, message, level="info"):
        colors = {
            "info": ("#0d1424", "#cbd5e1", "#1f2937"),
            "success": ("#0e1c16", "#34d399", "#16a34a"),
            "error": ("#1a0e13", "#fda4af", "#be123c"),
            "warning": ("#1f1a0c", "#fbbf24", "#92400e"),
        }
        bg, fg, border = colors.get(level, colors["info"])
        style = (
            f"padding: 12px; border: 1px solid {border}; border-radius: 12px; "
            f"background-color: {bg}; color: {fg}; font-weight: 600;"
        )
        self.message_label.setStyleSheet(style)
        self.message_label.setText(message)

    def show_ast_walk(self):
        if not self.current_expr:
            self.ast_output.setPlainText("Evaluate an expression to see how the circuit is built.")
            return

        try:
            # Capture output from visualize_ast_build
            old_stdout = sys.stdout
            sys.stdout = StringIO()

            input_order = extract_vars(self.current_expr)
            wire_map = {name: Wire() for name in input_order}
            build_circuit_ast(self.current_expr, wire_map, trace=True)

            output = sys.stdout.getvalue()
            sys.stdout = old_stdout

            formatted = self.pretty_build_output(output)
            self.ast_output.setHtml(formatted)
        except Exception as e:
            sys.stdout = old_stdout
            self.ast_output.setPlainText(f"Error: {str(e)}")

    def populate_step_simulation(self, expr, input_order, rows):
        header = [
            f"<b>Step-through Simulation</b>",
            f"<div style='color:#94a3b8;'>Expression: {html.escape(expr)}</div>",
            f"<div style='color:#94a3b8;'>Inputs: {', '.join(input_order)}</div>",
            "<br/>"
        ]
        body = []
        for i, row in enumerate(rows, start=1):
            inputs_str = ", ".join(f"{name}={row[name]}" for name in input_order)
            out_val = row["Output"]
            out_color = "#22c55e" if out_val else "#ef4444"
            body.append(
                f"<div style='margin-bottom:4px;'>"
                f"<span style='background:#1f2937;color:#e2e8f0;padding:4px 8px;border-radius:10px;font-weight:700;'>{i:02d}</span> "
                f"<span style='color:#cbd5e1;'>{inputs_str}</span> "
                f"<span style='margin-left:8px;padding:4px 10px;border-radius:10px;font-weight:800;background:{out_color};color:#0b1220;'>Output {out_val}</span> "
                f"<span style='color:#38bdf8;'>●→</span> "
                f"<span style='color:#cbd5e1;'>signal flow</span>"
                f"</div>"
            )
        html_content = "".join(header + body)
        self.step_output.setHtml(html_content)

    def on_truth_row_clicked(self, row, _col):
        if not self.last_input_order or row >= len(self.last_rows):
            return
        selected = self.last_rows[row]
        inputs_str = ", ".join(f"{k}={selected[k]}" for k in self.last_input_order)
        self.show_message(f"Row {row+1}: {inputs_str} -> Output={selected['Output']}", "info")
        # Step tab toggle removed; keep message only.

    def copy_text(self, text):
        clipboard = QGuiApplication.clipboard()
        clipboard.setText(text or "")
        self.show_message("Copied to clipboard.", "success")

    def set_header_tooltips(self, col_labels):
        for idx, label in enumerate(col_labels):
            item = self.truth_table.horizontalHeaderItem(idx)
            if not item:
                continue
            if label == "Output":
                item.setToolTip("Click to sort/group by output value.")
            else:
                item.setToolTip(f"Click to sort by {label}.")

    def on_header_clicked(self, index):
        if self.truth_table.columnCount() == 0:
            return
        output_idx = self.truth_table.columnCount() - 1
        if index == output_idx:
            self.output_sort_desc = not self.output_sort_desc
            order = Qt.SortOrder.DescendingOrder if self.output_sort_desc else Qt.SortOrder.AscendingOrder
            self.truth_table.sortItems(index, order)
        else:
            self.truth_table.sortItems(index, Qt.SortOrder.AscendingOrder)

    def rebuild_sandbox_toggles(self, input_order):
        while self.sandbox_toggle_row.count():
            item = self.sandbox_toggle_row.takeAt(0)
            widget = item.widget()
            if widget:
                widget.deleteLater()
        self.sandbox_toggles = {}
        if not input_order:
            self.sandbox_toggle_row.addWidget(QLabel("Evaluate an expression to enable toggles."))
            self.sandbox_toggle_row.addStretch()
            self.set_sandbox_badge("—", "#1f2937")
            return
        for name in input_order:
            cb = QCheckBox(name)
            cb.setStyleSheet("padding: 6px 8px;")
            cb.stateChanged.connect(self.update_sandbox_output)
            self.sandbox_toggles[name] = cb
            self.sandbox_toggle_row.addWidget(cb)
        fill_btn = QPushButton("All 0")
        fill_btn.setObjectName("pill")
        fill_btn.clicked.connect(lambda: self.set_all_toggles(False))
        self.sandbox_toggle_row.addWidget(fill_btn)
        fill_btn1 = QPushButton("All 1")
        fill_btn1.setObjectName("pill")
        fill_btn1.clicked.connect(lambda: self.set_all_toggles(True))
        self.sandbox_toggle_row.addWidget(fill_btn1)
        self.sandbox_toggle_row.addStretch()
        self.update_sandbox_output()

    def set_all_toggles(self, state):
        for cb in self.sandbox_toggles.values():
            cb.blockSignals(True)
            cb.setChecked(state)
            cb.blockSignals(False)
        self.update_sandbox_output()

    def update_sandbox_output(self):
        if not self.current_expr or not self.combo_map or not self.sandbox_toggles:
            self.set_sandbox_badge("—", "#1f2937")
            return
        combo = tuple(int(self.sandbox_toggles[name].isChecked()) for name in self.last_input_order)
        out_val = self.combo_map.get(combo)
        if out_val is None:
            self.set_sandbox_badge("?", "#f59e0b")
            self.show_message("Combination not found in table. Re-run evaluation.", "warning")
            return
        color = "#22c55e" if out_val else "#ef4444"
        self.set_sandbox_badge(str(out_val), color)

    def set_sandbox_badge(self, text, color):
        self.sandbox_output_label.setText(f"Output: {text}")
        self.sandbox_output_label.setStyleSheet(
            f"padding:6px 10px;border-radius:10px;font-weight:800;background:{color};color:#0b1220;"
        )

    def focus_sim_row(self, row_index):
        target = f"{row_index+1:02d} ▸"
        doc = self.step_output.document()
        cursor = doc.find(target)
        if cursor.isNull():
            return
        self.step_output.setTextCursor(cursor)
        self.step_output.ensureCursorVisible()

    def highlight_text(self, text_widget, term):
        doc = text_widget.document()
        cursor = QTextCursor(doc)
        selections = []
        if term:
            while True:
                cursor = doc.find(term, cursor)
                if cursor.isNull():
                    break
                sel = QTextEdit.ExtraSelection()
                fmt = QTextCharFormat()
                fmt.setBackground(QColor("#0ea5e9"))
                fmt.setForeground(QColor("#0b1220"))
                sel.cursor = cursor
                sel.format = fmt
                selections.append(sel)
        text_widget.setExtraSelections(selections)

    def clear_highlight(self, text_widget, input_field=None):
        text_widget.setExtraSelections([])
        if input_field is not None:
            input_field.clear()
        self.show_message("Cleared highlights.", "info")

    def build_gate_tree(self, expr):
        # Convert the parsed AST into a lightweight tree we can use for drawing.
        expr_ast = ast.parse(to_python_expr(expr), mode="eval")
        def walk(node):
            if isinstance(node, ast.Name):
                return {"label": node.id, "children": []}
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Invert):
                return {"label": "NOT", "children": [walk(node.operand)]}
            if isinstance(node, ast.BinOp):
                op_label = "UNKNOWN"
                if isinstance(node.op, ast.BitAnd): op_label = "AND"
                elif isinstance(node.op, ast.BitOr): op_label = "OR"
                elif isinstance(node.op, ast.BitXor): op_label = "XOR"
                elif isinstance(node.op, ast.Mod): op_label = "NAND"
                elif isinstance(node.op, ast.LShift): op_label = "NOR"
                elif isinstance(node.op, ast.RShift): op_label = "XNOR"
                return {"label": op_label, "children": [walk(node.left), walk(node.right)]}
            if isinstance(node, ast.Call):
                fname = node.func.id.upper()
                return {"label": fname, "children": [walk(arg) for arg in node.args]}
            raise ValueError("Unsupported expression for diagram")
        return walk(expr_ast.body)

    def get_gate_color(self, gate):
        return {
            "NOT": QColor("#f59e0b"),
            "AND": QColor("#22c55e"),
            "OR": QColor("#38bdf8"),
            "XOR": QColor("#a855f7"),
            "NAND": QColor("#f97316"),
            "NOR": QColor("#e11d48"),
            "XNOR": QColor("#10b981"),
        }.get(gate, QColor("#38bdf8"))

    def layout_tree(self, root):
        """
        Left-to-right layout with inputs on the left (depth=0) and output on the right.
        Depth is computed bottom-up so leaves sit at x=0.
        """
        positions = {}
        y_step = 90
        x_step = 150
        x_margin = 60
        y_margin = 40
        y_cursor = 0

        depth_map = {}
        def compute_depth(node):
            if not node.get("children"):
                depth_map[id(node)] = 0
                return 0
            d = 1 + max(compute_depth(c) for c in node["children"])
            depth_map[id(node)] = d
            return d
        max_depth = compute_depth(root)

        def assign_y(node):
            nonlocal y_cursor
            if not node.get("children"):
                y = y_margin + y_cursor * y_step
                y_cursor += 1
            else:
                child_ys = []
                for child in node["children"]:
                    assign_y(child)
                    child_ys.append(positions[id(child)].y())
                y = sum(child_ys) / len(child_ys) if child_ys else y_margin
            depth = depth_map[id(node)]
            x = x_margin + depth * x_step
            positions[id(node)] = QPointF(x, y)

        assign_y(root)
        return positions

    def render_gate_diagram(self, root):
        positions = self.layout_tree(root)
        if not positions:
            return None
        xs = [p.x() for p in positions.values()]
        ys = [p.y() for p in positions.values()]
        width = int((max(xs) if xs else 0) + 220)
        height = int((max(ys) if ys else 0) + 160)
        pix = QPixmap(max(1, width), max(1, height))
        pix.fill(QColor("#0c1220"))
        painter = QPainter(pix)
        if not painter.isActive():
            return pix
        try:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)

            rect_w, rect_h = 110, 60
            leaf_r = 18

            def is_leaf(node):
                return len(node.get("children", [])) == 0

            def draw_edges(node):
                p1 = positions[id(node)]
                start_offset = QPointF(rect_w / 2 if not is_leaf(node) else leaf_r, 0)
                for child in node["children"]:
                    p2 = positions[id(child)]
                    end_offset = QPointF(rect_w / 2, 0) if not is_leaf(child) else QPointF(leaf_r, 0)
                    pen = QPen(QColor("#334155"), 2)
                    painter.setPen(pen)
                    start_point = p1 + start_offset
                    end_point = p2 - end_offset
                    mid_x = (start_point.x() + end_point.x()) / 2
                    painter.drawLine(start_point, QPointF(mid_x, start_point.y()))
                    painter.drawLine(QPointF(mid_x, start_point.y()), QPointF(mid_x, end_point.y()))
                    painter.drawLine(QPointF(mid_x, end_point.y()), end_point)
                    draw_edges(child)

            def draw_gate_shape(painter, x, y, w, h, gate_type):
                path = QPainterPath()
                
                # Basic shapes
                if gate_type == "NOT":
                    # Triangle
                    path.moveTo(x, y)
                    path.lineTo(x, y + h)
                    path.lineTo(x + w - 10, y + h / 2)
                    path.closeSubpath()
                    # Circle at tip
                    painter.drawPath(path)
                    painter.drawEllipse(QPointF(x + w - 5, y + h / 2), 5, 5)
                    return

                elif gate_type == "AND" or gate_type == "NAND":
                    # Flat back, curved front
                    path.moveTo(x, y)
                    path.lineTo(x + w / 2, y)
                    path.arcTo(x, y, w, h, 90, -180)
                    path.lineTo(x, y + h)
                    path.closeSubpath()
                    
                elif gate_type == "OR" or gate_type == "NOR":
                    # Curved back, pointed front
                    path.moveTo(x, y)
                    path.quadTo(x + w / 4, y + h / 2, x, y + h)
                    path.quadTo(x + w / 2, y + h, x + w, y + h / 2)
                    path.quadTo(x + w / 2, y, x, y)
                    path.closeSubpath()

                elif gate_type == "XOR" or gate_type == "XNOR":
                    # OR shape with extra line and slightly wider body
                    shift = 8
                    path.moveTo(x + shift, y)
                    path.quadTo(x + shift + w / 4, y + h / 2, x + shift, y + h)
                    path.quadTo(x + shift + w / 2, y + h, x + w + 8, y + h / 2)
                    path.quadTo(x + shift + w / 2, y, x + shift, y)
                    path.closeSubpath()
                    
                    # Extra line at back
                    back_line = QPainterPath()
                    back_line.moveTo(x, y)
                    back_line.quadTo(x + w / 4, y + h / 2, x, y + h)
                    painter.drawPath(back_line)

                else:
                    # Fallback rectangle
                    painter.drawRoundedRect(x, y, w, h, 4, 4)
                    return

                painter.drawPath(path)
                
                # Add circle for negated outputs
                if gate_type in ["NAND", "NOR", "XNOR"]:
                    painter.drawEllipse(QPointF(x + w + 5, y + h / 2), 5, 5)


            def draw_nodes(node):
                pos = positions[id(node)]

                if is_leaf(node):
                    painter.setBrush(QBrush(QColor("#e0f2fe")))
                    painter.setPen(QPen(QColor("#38bdf8"), 2))
                    painter.drawEllipse(pos, leaf_r, leaf_r)
                    painter.setPen(QPen(QColor("#0b1220"), 1))
                    font = painter.font()
                    font.setBold(True)
                    font.setPointSize(10)
                    painter.setFont(font)
                    text_rect = QRectF(pos.x() - leaf_r, pos.y() - leaf_r, leaf_r * 2, leaf_r * 2)
                    painter.drawText(text_rect, int(Qt.AlignmentFlag.AlignCenter), node["label"])
                else:
                    color = self.get_gate_color(node["label"])
                    painter.setBrush(QBrush(color))
                    painter.setPen(QPen(QColor("#cbd5e1"), 2))

                    top_left_x = pos.x() - rect_w/2
                    top_left_y = pos.y() - rect_h/2

                    draw_gate_shape(painter, top_left_x, top_left_y, rect_w, rect_h, node["label"])

                    painter.setPen(QPen(QColor("#0b1220"), 1))
                    font = painter.font()
                    font.setBold(True)
                    font.setPointSize(9)
                    painter.setFont(font)

                    text_rect = QRectF(top_left_x, top_left_y, rect_w, rect_h)
                    painter.drawText(text_rect, int(Qt.AlignmentFlag.AlignCenter), node["label"])

                for child in node["children"]:
                    draw_nodes(child)

            draw_edges(root)
            draw_nodes(root)

            # Output tap on the right of the root
            root_pos = positions[id(root)]
            out_x = root_pos.x() + rect_w / 2 + 16
            out_y = root_pos.y()
            painter.setPen(QPen(QColor("#cbd5e1"), 2))
            painter.drawLine(root_pos + QPointF(rect_w / 2, 0), QPointF(out_x, out_y))
            painter.setBrush(QBrush(QColor("#e0f2fe")))
            painter.setPen(QPen(QColor("#38bdf8"), 2))
            out_r = 18
            center = QPointF(out_x + out_r, out_y)
            painter.drawEllipse(center, out_r, out_r)
            painter.setPen(QPen(QColor("#0b1220"), 1))
            font = painter.font()
            font.setBold(True)
            font.setPointSize(9)
            painter.setFont(font)
            text_rect = QRectF(center.x() - out_r, center.y() - out_r, out_r * 2, out_r * 2)
            painter.drawText(text_rect, int(Qt.AlignmentFlag.AlignCenter), "OUT")
        except Exception:
            return pix
        finally:
            painter.end()
        return pix

    def update_gate_diagram(self, expr):
        try:
            # Build an AST tree, convert to a simple node tree, and render a left-to-right schematic.
            tree = self.build_gate_tree(expr)
            pix = self.render_gate_diagram(tree)
            if pix:
                # Scale to fit height, keeping aspect ratio
                max_h = 320
                if pix.height() > max_h:
                    pix = pix.scaledToHeight(max_h, Qt.TransformationMode.SmoothTransformation)
                self.diagram_label.setPixmap(pix)
            else:
                self.diagram_label.setText("Diagram unavailable (render issue).")
        except Exception as e:
            self.diagram_label.setText(f"Diagram unavailable: {e}")

    def show_cheatsheet(self):
        cheatsheet = (
            "Operators:\n"
            "! NOT    * AND    + OR\n"
            "^ XOR    % NAND   ~ NOR   # XNOR\n"
            "Tips:\n"
            "- Wrap groups: (A+B)*!C\n"
            "- Functions: XOR(A, B) also works\n"
            "- Use live evaluate to see changes instantly"
        )
        QMessageBox.information(self, "Boolean Cheatsheet", cheatsheet)

    def register_shortcuts(self):
        for seq in ["Ctrl+L", "Meta+L"]:
            QShortcut(QKeySequence(seq), self, activated=self.toggle_live_mode)
        for seq in ["Ctrl+/", "Meta+/"]:
            QShortcut(QKeySequence(seq), self, activated=self.show_cheatsheet)

    def toggle_live_mode(self):
        self.live_toggle.setChecked(not self.live_toggle.isChecked())
        state = "on" if self.live_toggle.isChecked() else "off"
        self.show_message(f"Live evaluate turned {state}.", "info")

    def pretty_build_output(self, raw_output):
        lines = raw_output.splitlines()
        steps = []
        output_label = None
        for line in lines:
            step_match = re.search(r"(W\d+\s*=.*)", line)
            if step_match:
                steps.append(step_match.group(1).strip())
            out_match = re.search(r"Output:\s*(.+)", line)
            if out_match:
                output_label = out_match.group(1).strip()
        gate_colors = {
            "NOT": "#f59e0b",
            "AND": "#22c55e",
            "OR": "#38bdf8",
            "XOR": "#a855f7",
            "NAND": "#f97316",
            "NOR": "#e11d48",
            "XNOR": "#10b981",
        }
        header = (
            f"<div><b>Build for:</b> {html.escape(self.current_expr)}</div>"
            f"<div style='color:#94a3b8;'>Inputs: {', '.join(self.last_input_order) if self.last_input_order else '—'}</div>"
            f"<div style='color:#94a3b8;'>Output node: {html.escape(output_label) if output_label else '—'}</div>"
            f"<div style='color:#94a3b8;'>Gate count: {len(steps)}</div><br/>"
        )
        if not steps:
            return header + "<div>No gate steps available.</div>"
        body = []
        for i, s in enumerate(steps, 1):
            gate_type = "GATE"
            for key in gate_colors.keys():
                if key in s:
                    gate_type = key
                    break
            color = gate_colors.get(gate_type, "#38bdf8")
            body.append(
                f"<div style='margin-bottom:4px;'>"
                f"<span style='background:#1f2937;color:#e2e8f0;padding:4px 8px;border-radius:10px;font-weight:700;'>{i:02d}</span> "
                f"<span style='padding:4px 10px;border-radius:10px;font-weight:800;background:{color};color:#0b1220;'>{gate_type}</span> "
                f"<span style='color:#cbd5e1;'>{html.escape(s)}</span>"
                f"</div>"
            )
        return header + "".join(body)


if __name__ == "__main__":
    if HAS_PYQT:
        app = QApplication(sys.argv)
        window = CircuitSimGUI()
        window.show()
        sys.exit(app.exec())
    else:
        # Fallback to console mode
        expr = input("Enter a logical expression (use !, *, +, ^, %, ~, #): ")

        # 1. Console based truth table - Core functionality
        evaluate(expr)

        # 2. Prompt user if they want to see the AST build (visualisation)
        show_ast = input("\nShow AST walk and circuit construction? (y/n): ").strip().lower()
        if show_ast == "y":
            visualize_ast_build(expr)

        # 3. Ask for extra visualisations (w/ matplotlib)
        show_plots = input("\nShow matplotlib visualisations (if available)? (y/n): ").strip().lower()
        if show_plots == "y":
            plot_truth_table(expr)
            step_simulation(expr)
            plot_output_distribution(expr)
