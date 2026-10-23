import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from tkcalendar import Calendar
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import pandas as pd
from datetime import datetime, timedelta
import numpy as np
import json
import xml.etree.ElementTree as ET
import xml.dom.minidom
import textwrap
import networkx as nx

class ToolTip:
    """Κλάση για τη δημιουργία μονολεκτικών tooltips στα κουμπιά"""
    def __init__(self, widget, text):
        self.widget = widget
        self.text = text
        self.tipwindow = None
        self.id = None
        self.x = self.y = 0
        self.widget.bind("<Enter>", self.show_tip)
        self.widget.bind("<Leave>", self.hide_tip)

    def show_tip(self, event=None):
        self.schedule_tip()

    def hide_tip(self, event=None):
        self.unschedule_tip()
        self.destroy_tip()

    def schedule_tip(self):
        self.unschedule_tip()
        self.id = self.widget.after(400, self.display_tip)

    def unschedule_tip(self):
        id_val = self.id
        self.id = None
        if id_val:
            self.widget.after_cancel(id_val)

    def display_tip(self):
        if self.tipwindow:
            return
        x = self.widget.winfo_rootx() + 10
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 5
        self.tipwindow = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        label = tk.Label(tw, text=self.text, background="#FFFEE0", relief='solid', borderwidth=1,
                         font=("Arial", 9, "normal"), padx=4, pady=2)
        label.pack(ipadx=1)

    def destroy_tip(self):
        tw = self.tipwindow
        self.tipwindow = None
        if tw:
            tw.destroy()


class GanttApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Διάγραμμα Gantt")
        self.root.geometry("1450x850")
        
        # Άνοιγμα σε maximized κατάσταση
        self.root.state('zoomed')

        # Διαχείριση κλεισίματος παραθύρου (πλήκτρο Χ ή Exit)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close_application)

        self.selected_item_id = None
        self.canvas_widget = None
        self.fig = None
        self.ax = None
        self.task_rects = []
        self.holiday_rects = []
        self.current_file_path = None
        
        # Συντελεστής Zoom για το πλάτος του διαγράμματος (προεπιλογή 1.0)
        self.zoom_factor = 1.0
        
        # Μεταβλητές κατάστασης για τη λειτουργία PAN (Μετακίνηση με σύρσιμο)
        self.pan_active = False
        self.is_panning = False
        self.pan_start_x = 0
        self.pan_start_y = 0
        
        self.deleted_holidays_stack = []
        self.deleted_tasks_stack = []
        self.form_history_stack = []

        self.tasks = []
        self.holidays = []
        
        # Κατάσταση ταξινόμησης πίνακα αργιών
        self.hol_sort_col = "Date"
        self.hol_sort_reverse = False

        # --- ΓΡΑΜΜΗ ΜΕΝΟΥ (Windows Style) ---
        menubar = tk.Menu(self.root)
        
        # File Menu
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open", command=self.load_project, accelerator="Ctrl+O")
        file_menu.add_command(label="Save", command=self.save_project, accelerator="Ctrl+S")
        file_menu.add_command(label="Export to XML", command=self.export_to_xml, accelerator="Ctrl+Shift+S")
        file_menu.add_command(label="Export Flow Diagram to Image", command=self.export_network_diagram, accelerator="Ctrl+Shift+D")
        file_menu.add_separator()
        file_menu.add_command(label="Print to PDF", command=self.export_to_pdf, accelerator="Ctrl+P")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_close_application)
        menubar.add_cascade(label="File", menu=file_menu)

        # Bind shortcuts
        self.root.bind("<Control-o>", lambda e: self.load_project())
        self.root.bind("<Control-O>", lambda e: self.load_project())
        self.root.bind("<Control-s>", lambda e: self.save_project())
        self.root.bind("<Control-S>", lambda e: self.save_project())
        self.root.bind("<Control-Shift-S>", lambda e: self.export_to_xml())
        self.root.bind("<Control-Shift-D>", lambda e: self.export_network_diagram())
        self.root.bind("<Control-p>", lambda e: self.export_to_pdf())
        self.root.bind("<Control-P>", lambda e: self.export_to_pdf())
        self.root.bind("<Control-d>", lambda e: self.show_network_diagram())
        self.root.bind("<Control-D>", lambda e: self.show_network_diagram())

        edit_menu = tk.Menu(menubar, tearoff=0)
        edit_menu.add_command(label="Undo Task Delete", command=self.undo_delete_task)
        edit_menu.add_command(label="Undo Season Delete", command=self.undo_delete_holiday)
        menubar.add_cascade(label="Edit", menu=edit_menu)

        # View Menu
        self.toolbar_visible = tk.BooleanVar(value=True)
        self.zoombar_visible = tk.BooleanVar(value=True)

        view_menu = tk.Menu(menubar, tearoff=0)
        view_menu.add_command(label="Zoom In", command=self.zoom_in)
        view_menu.add_command(label="Zoom Out", command=self.zoom_out)
        view_menu.add_command(label="Reset Zoom (100%)", command=self.zoom_reset)
        view_menu.add_command(label="Fit to Screen", command=self.fit_to_screen)
        view_menu.add_separator()
        view_menu.add_command(label="Show Flow/Network Diagram", command=self.show_network_diagram, accelerator="Ctrl+D")
        view_menu.add_separator()
        view_menu.add_checkbutton(label="Εμφάνιση Παλέτας Αρχείου", variable=self.toolbar_visible, command=self.toggle_toolbar)
        view_menu.add_checkbutton(label="Εμφάνιση Μπάρας Zoom", variable=self.zoombar_visible, command=self.toggle_zoombar)
        menubar.add_cascade(label="View", menu=view_menu)

        # Help & About Menu
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="Help & Instructions", command=self.open_help_window)
        help_menu.add_separator()
        help_menu.add_command(label="About", command=self.open_about_window)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menubar)

        # --- ΑΡΙΣΤΕΡΟ ΠΛΑΙΣΙΟ (Φόρμες & Χειριστήρια) ---
        self.control_frame = ttk.LabelFrame(root, text=" Διαχείριση Έργου & Αρχείου ")
        self.control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)

        # Έγχρωμη Παλέτα Αρχείου
        self.file_toolbar_frame = ttk.Frame(self.control_frame)
        self.file_toolbar_frame.pack(fill=tk.X, padx=10, pady=4)

        style = ttk.Style()
        style.configure("Open.TButton", foreground="#1B4F72", font=("Arial", 12, "bold"))
        style.configure("Save.TButton", foreground="#196F3D", font=("Arial", 12, "bold"))
        style.configure("Xml.TButton", foreground="#D35400", font=("Arial", 12, "bold"))
        style.configure("Flow.TButton", foreground="#2471A3", font=("Arial", 12, "bold"))
        style.configure("Print.TButton", foreground="#7D3C98", font=("Arial", 12, "bold"))
        style.configure("Help.TButton", foreground="#B7950B", font=("Arial", 12, "bold"))
        style.configure("Exit.TButton", foreground="#C0392B", font=("Arial", 12, "bold"))

        open_btn = ttk.Button(self.file_toolbar_frame, text="📁", width=3, command=self.load_project, style="Open.TButton")
        open_btn.pack(side=tk.LEFT, padx=(0, 2))
        ToolTip(open_btn, "Άνοιγμα")

        save_btn = ttk.Button(self.file_toolbar_frame, text="💾", width=3, command=self.save_project, style="Save.TButton")
        save_btn.pack(side=tk.LEFT, padx=2)
        ToolTip(save_btn, "Αποθήκευση")

        xml_btn = ttk.Button(self.file_toolbar_frame, text="📄", width=3, command=self.export_to_xml, style="Xml.TButton")
        xml_btn.pack(side=tk.LEFT, padx=2)
        ToolTip(xml_btn, "Εξαγωγή XML")

        flow_btn = ttk.Button(self.file_toolbar_frame, text="🔀", width=3, command=self.show_network_diagram, style="Flow.TButton")
        flow_btn.pack(side=tk.LEFT, padx=2)
        ToolTip(flow_btn, "Διάγραμμα Ροής/Δικτύου")

        print_btn = ttk.Button(self.file_toolbar_frame, text="🖨️", width=3, command=self.export_to_pdf, style="Print.TButton")
        print_btn.pack(side=tk.LEFT, padx=2)
        ToolTip(print_btn, "Εκτύπωση")

        help_btn = ttk.Button(self.file_toolbar_frame, text="❓", width=3, command=self.open_help_window, style="Help.TButton")
        help_btn.pack(side=tk.LEFT, padx=2)
        ToolTip(help_btn, "Βοήθεια")

        exit_btn = ttk.Button(self.file_toolbar_frame, text="🚪", width=3, command=self.on_close_application, style="Exit.TButton")
        exit_btn.pack(side=tk.RIGHT, padx=(2, 0))
        ToolTip(exit_btn, "Έξοδος")

        # Ετικέτα διαδρομής αρχείου
        self.file_path_label = ttk.Label(self.control_frame, text="Αρχείο: [ Κανένα / Νέο Έργο ]", font=("Arial", 8), foreground="#555555")
        self.file_path_label.pack(anchor="w", padx=10, pady=2, fill=tk.X)

        ttk.Separator(self.control_frame, orient='horizontal').pack(fill='x', padx=10, pady=8)

        # --- ΠΕΔΙΟ: Τίτλος Έργου ---
        ttk.Label(self.control_frame, text="Έργο:", font=("Arial", 9, "bold")).pack(anchor="w", padx=10, pady=(2, 2))

        self.proj_title_entry = ttk.Entry(self.control_frame)
        self.proj_title_entry.pack(anchor="w", padx=10, pady=2, fill=tk.X)
        self.proj_title_entry.bind("<Return>", lambda e: self.update_plot())
        self.proj_title_entry.bind("<FocusOut>", lambda e: self.update_plot())

        # 0.1 Έναρξη Έργου
        ttk.Label(self.control_frame, text="Έναρξη έργου:", font=("Arial", 9, "bold")).pack(anchor="w", padx=10, pady=(6, 2))
        
        proj_start_frame = ttk.Frame(self.control_frame)
        proj_start_frame.pack(anchor="w", padx=10, pady=2, fill=tk.X)
        
        self.proj_start_entry = ttk.Entry(proj_start_frame, width=15)
        self.proj_start_entry.pack(side=tk.LEFT, padx=(0, 2))
        self.proj_start_entry.insert(0, datetime.now().strftime("%Y-%m-%d"))

        pick_proj_start_btn = ttk.Button(proj_start_frame, text="📅", width=4, command=self.open_proj_calendar_popup)
        pick_proj_start_btn.pack(side=tk.LEFT)

        ttk.Separator(self.control_frame, orient='horizontal').pack(fill='x', padx=10, pady=8)

        # 1. ΕΝΟΤΗΤΑ: Υποέργα
        top_inputs_frame = ttk.Frame(self.control_frame)
        top_inputs_frame.pack(anchor="w", padx=10, pady=2, fill=tk.X)

        left_input_container = ttk.Frame(top_inputs_frame)
        left_input_container.pack(side=tk.LEFT, padx=(0, 5))
        
        ttk.Label(left_input_container, text="Υποέργο:", font=("Arial", 9, "bold")).pack(anchor="w", pady=(2, 2))
        self.task_entry = ttk.Entry(left_input_container, width=11)
        self.task_entry.pack(anchor="w", pady=2)

        right_input_container = ttk.Frame(top_inputs_frame)
        right_input_container.pack(side=tk.LEFT, expand=True, fill=tk.X)
        
        ttk.Label(right_input_container, text="Τίτλος:", font=("Arial", 9, "bold")).pack(anchor="w", pady=(2, 2))
        self.title_entry = ttk.Entry(right_input_container, width=15)
        self.title_entry.pack(anchor="w", fill=tk.X, pady=2)

        # Διάρκεια και Προαπαιτούμενο στην ίδια γραμμή
        dur_pre_container = ttk.Frame(self.control_frame)
        dur_pre_container.pack(anchor="w", padx=10, pady=(2, 2), fill=tk.X)

        dur_box_frame = ttk.Frame(dur_pre_container)
        dur_box_frame.pack(side=tk.LEFT, padx=(0, 10))

        ttk.Label(dur_box_frame, text="Διάρκεια:", font=("Arial", 9, "bold")).pack(anchor="w", pady=(2, 2))
        self.duration_entry = ttk.Entry(dur_box_frame, width=11)
        self.duration_entry.pack(anchor="w", pady=2)

        pre_box_frame = ttk.Frame(dur_pre_container)
        pre_box_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)

        ttk.Label(pre_box_frame, text="Προαπαιτούμενο:", font=("Arial", 9, "bold")).pack(anchor="w", pady=(2, 2))
        
        pre_sub_frame = ttk.Frame(pre_box_frame)
        pre_sub_frame.pack(anchor="w", fill=tk.X, pady=2)

        self.pre_entry = ttk.Entry(pre_sub_frame, width=11)
        self.pre_entry.pack(side=tk.LEFT, padx=(0, 2))
        self.pre_entry.insert(0, "-")

        add_pre_btn = ttk.Button(pre_sub_frame, text="Add", width=4, command=self.open_multi_pre_popup)
        add_pre_btn.pack(side=tk.LEFT)

        btn_frame = ttk.Frame(self.control_frame)
        btn_frame.pack(fill=tk.X, padx=10, pady=8)

        self.save_btn = ttk.Button(btn_frame, text="Προσθήκη Υποέργου", command=self.save_task)
        self.save_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 3))

        self.undo_form_btn = ttk.Button(btn_frame, text="Αναίρεση", command=self.undo_form_action, state=tk.DISABLED)
        self.undo_form_btn.pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(3, 0))

        # Λίστα Υποέργων
        ttk.Label(self.control_frame, text="Υποέργα:", font=("Arial", 9, "bold")).pack(anchor="w", padx=10, pady=(2, 2))
        
        tree_frame = ttk.Frame(self.control_frame)
        tree_frame.pack(padx=10, pady=2, fill=tk.BOTH, expand=True)
        
        self.tree = ttk.Treeview(tree_frame, columns=("Task", "Title", "Pre", "Start", "End", "Duration", "EF", "LF", "Slack"), show="headings", height=5)
        self.tree.heading("Task", text="Υπ")
        self.tree.heading("Title", text="Τίτλος")
        self.tree.heading("Pre", text="Προ")
        self.tree.heading("Start", text="Έναρξη")
        self.tree.heading("End", text="Πέρας")
        self.tree.heading("Duration", text="Διάρκεια")
        self.tree.heading("EF", text="EF")
        self.tree.heading("LF", text="LF")
        self.tree.heading("Slack", text="Slack")
        
        self.tree.column("Task", width=30, anchor="center")
        self.tree.column("Title", width=75, anchor="w")
        self.tree.column("Pre", width=30, anchor="center")
        self.tree.column("Start", width=65, anchor="center")
        self.tree.column("End", width=65, anchor="center")
        self.tree.column("Duration", width=45, anchor="center")
        self.tree.column("EF", width=25, anchor="center")
        self.tree.column("LF", width=25, anchor="center")
        self.tree.column("Slack", width=30, anchor="center")
        
        self.tree.bind("<<TreeviewSelect>>", self.prepare_edit)
        
        scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscroll=scrollbar.set)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        task_btn_frame = ttk.Frame(self.control_frame)
        task_btn_frame.pack(fill=tk.X, padx=10, pady=5)

        move_up_btn = ttk.Button(task_btn_frame, text="⬆️ Up", command=lambda: self.move_task(-1))
        move_up_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))

        move_down_btn = ttk.Button(task_btn_frame, text="⬇️ Down", command=lambda: self.move_task(1))
        move_down_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 2))

        del_btn = ttk.Button(task_btn_frame, text="Διαγραφή", command=self.delete_task)
        del_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 2))

        self.undo_task_btn = ttk.Button(task_btn_frame, text="↩️ Αναίρεση", command=self.undo_delete_task, state=tk.DISABLED)
        self.undo_task_btn.pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2, 0))

        # Πληροφορίες Έργου
        info_frame = ttk.LabelFrame(self.control_frame, text=" Διάρκεια Έργου: ")
        info_style = ttk.Style()
        info_style.configure("Bold.TLabelframe.Label", font=("Arial", 9, "bold"))
        info_frame.configure(style="Bold.TLabelframe")
        info_frame.pack(fill=tk.X, padx=10, pady=5)

        lbl1 = ttk.Label(info_frame, text="Διάρκεια Έργου ΧΩΡΙΣ αργίες:", font=("Arial", 9))
        lbl1.grid(row=0, column=0, sticky="w", padx=5, pady=2)
        self.val_no_holidays = ttk.Label(info_frame, text="0 ημέρες", font=("Arial", 9), anchor="e")
        self.val_no_holidays.grid(row=0, column=1, sticky="e", padx=5, pady=2)

        lbl2 = ttk.Label(info_frame, text="Σύνολο αργιών:", font=("Arial", 9))
        lbl2.grid(row=1, column=0, sticky="w", padx=5, pady=2)
        self.val_holidays_count = ttk.Label(info_frame, text="0 ημέρες", font=("Arial", 9), anchor="e")
        self.val_holidays_count.grid(row=1, column=1, sticky="e", padx=5, pady=2)

        lbl3 = ttk.Label(info_frame, text="Συνολική Διάρκεια Έργου:", font=("Arial", 9))
        lbl3.grid(row=2, column=0, sticky="w", padx=5, pady=2)
        self.val_with_holidays = ttk.Label(info_frame, text="0 ημέρες", font=("Arial", 9), anchor="e")
        self.val_with_holidays.grid(row=2, column=1, sticky="e", padx=5, pady=2)

        lbl_cpm = ttk.Label(info_frame, text="Critical Path:", font=("Arial", 9, "bold"))
        lbl_cpm.grid(row=3, column=0, sticky="w", padx=5, pady=2)
        
        self.val_cpm_path = ttk.Label(info_frame, text="-", font=("Arial", 9, "bold"), foreground="#27AE60", anchor="w")
        self.val_cpm_path.grid(row=3, column=1, sticky="w", padx=5, pady=2)

        info_frame.columnconfigure(0, weight=1)

        ttk.Separator(self.control_frame, orient='horizontal').pack(fill='x', padx=10, pady=5)

        # 2. ΕΝΟΤΗΤΑ: Διαχείριση Αργιών
        ttk.Label(self.control_frame, text="Αργίες:", font=("Arial", 9, "bold")).pack(anchor="w", padx=10, pady=(4, 2))

        day_buttons_frame = ttk.Frame(self.control_frame)
        day_buttons_frame.pack(fill=tk.X, padx=10, pady=(2, 6))

        days_labels = [("Δ", 0), ("Τ", 1), ("Τ", 2), ("Π", 3), ("Π", 4), ("Σ", 5), ("Κ", 6)]
        self.day_vars = {}
        self.day_buttons = {}

        for label, day_num in days_labels:
            var = tk.BooleanVar(value=False)
            self.day_vars[day_num] = var
            
            btn = tk.Checkbutton(
                day_buttons_frame, 
                text=label, 
                variable=var, 
                indicatoron=False, 
                width=3, 
                font=("Arial", 9, "bold"),
                fg="black",
                selectcolor="#FFF1A5",
                command=lambda d=day_num: self.on_day_button_toggle(d)
            )
            btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
            self.day_buttons[day_num] = btn

        hol_list_frame = ttk.Frame(self.control_frame)
        hol_list_frame.pack(padx=10, pady=2, fill=tk.BOTH, expand=True)
        
        self.hol_tree = ttk.Treeview(hol_list_frame, columns=("Day", "Date"), show="headings", height=4)
        self.hol_tree.heading("Day", text="Ημέρα ↕", command=lambda: self.sort_holidays_column("Day"))
        self.hol_tree.heading("Date", text="Ημερομηνία 🔽", command=lambda: self.sort_holidays_column("Date"))
        
        self.hol_tree.column("Day", width=85, anchor="w")
        self.hol_tree.column("Date", width=115, anchor="center")
        
        hol_scrollbar = ttk.Scrollbar(hol_list_frame, orient=tk.VERTICAL, command=self.hol_tree.yview)
        self.hol_tree.configure(yscroll=hol_scrollbar.set)
        self.hol_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        hol_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Κουμπιά Season / Holidays
        hol_btn_frame = ttk.Frame(self.control_frame)
        hol_btn_frame.pack(fill=tk.X, padx=10, pady=(2, 8))

        add_hol_btn = ttk.Button(hol_btn_frame, text="Add", command=self.open_calendar_popup)
        add_hol_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 1))

        range_hol_btn = ttk.Button(hol_btn_frame, text="Season", command=self.open_holiday_range_popup)
        range_hol_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)

        del_hol_btn = ttk.Button(hol_btn_frame, text="DEL", command=self.delete_holiday)
        del_hol_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)

        self.undo_hol_btn = ttk.Button(hol_btn_frame, text="Undo", command=self.undo_delete_holiday, state=tk.DISABLED)
        self.undo_hol_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(1, 0))

        # --- ΔΕΞΙ ΠΛΑΙΣΙΟ ---
        outer_plot_frame = ttk.Frame(root)
        outer_plot_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Zoom Toolbar (εμφανιζόμενο/αποκρυπτόμενο)
        self.zoom_toolbar = ttk.Frame(outer_plot_frame)
        self.zoom_toolbar.pack(side=tk.TOP, fill=tk.X, pady=(0, 5))

        ttk.Label(self.zoom_toolbar, text="🔍 Zoom:", font=("Arial", 9, "bold")).pack(side=tk.LEFT, padx=(0, 6))

        zoom_in_btn = ttk.Button(self.zoom_toolbar, text="➕ Zoom In", width=9, command=self.zoom_in)
        zoom_in_btn.pack(side=tk.LEFT, padx=2)

        zoom_out_btn = ttk.Button(self.zoom_toolbar, text="➖ Zoom Out", width=9, command=self.zoom_out)
        zoom_out_btn.pack(side=tk.LEFT, padx=2)

        self.zoom_entry_var = tk.StringVar(value="100")
        self.zoom_entry = ttk.Entry(self.zoom_toolbar, textvariable=self.zoom_entry_var, width=5, justify="center")
        self.zoom_entry.pack(side=tk.LEFT, padx=4)
        self.zoom_entry.bind("<Return>", self.on_zoom_entry_changed)

        zoom_reset_btn = ttk.Button(self.zoom_toolbar, text="100%", width=5, command=self.zoom_reset)
        zoom_reset_btn.pack(side=tk.LEFT, padx=2)

        fit_screen_btn = ttk.Button(self.zoom_toolbar, text="⛶ Fit to Screen", width=12, command=self.fit_to_screen)
        fit_screen_btn.pack(side=tk.LEFT, padx=6)

        self.pan_btn = ttk.Button(self.zoom_toolbar, text="✋ Pan", width=7, command=self.toggle_pan)
        self.pan_btn.pack(side=tk.LEFT, padx=6)

        canvas_container = ttk.Frame(outer_plot_frame)
        canvas_container.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.plot_canvas = tk.Canvas(canvas_container, highlightthickness=0)
        self.plot_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        v_scroll = ttk.Scrollbar(canvas_container, orient=tk.VERTICAL, command=self.plot_canvas.yview)
        v_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        h_scroll = ttk.Scrollbar(outer_plot_frame, orient=tk.HORIZONTAL, command=self.plot_canvas.xview)
        h_scroll.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 0))

        self.plot_canvas.configure(yscrollcommand=v_scroll.set, xscrollcommand=h_scroll.set)

        self.plot_frame = ttk.Frame(self.plot_canvas)
        self.plot_canvas_window = self.plot_canvas.create_window((0, 0), window=self.plot_frame, anchor="nw")

        self.plot_frame.bind("<Configure>", self.on_plot_frame_configure)
        self.plot_canvas.bind("<Configure>", self.on_canvas_configure)

        self.plot_canvas.bind_all("<MouseWheel>", self._on_mouse_wheel)
        self.plot_canvas.bind_all("<Shift-MouseWheel>", self._on_shift_mouse_wheel)

        self.update_tree()
        self.update_holidays_tree()
        self.update_plot()

        # Αυτόματη προσαρμογή Fit to Screen μόλις ανοίξει η εφαρμογή
        self.root.after(100, self.fit_to_screen)

    def generate_network_figure(self):
        """Κοινή μέθοδος δημιουργίας του figure για το διάγραμμα ροής"""
        fig, ax = plt.subplots(figsize=(12, 8))
        G = nx.DiGraph()

        _, _, slack_map = self.calculate_cpm_details()

        predecessors_map = {}
        for t in self.tasks:
            t_name = t["Task"]
            raw_pre = t.get("Pre", "-")
            preds = [p.strip() for p in raw_pre.split(",") if p.strip() and p != "-"]
            predecessors_map[t_name] = preds
            G.add_node(t_name, critical=(slack_map.get(t_name, 0) == 0))

        levels = {}
        def get_node_level(node):
            if node in levels:
                return levels[node]
            preds = predecessors_map.get(node, [])
            if not preds:
                levels[node] = 0
            else:
                levels[node] = max(get_node_level(p) for p in preds if p in predecessors_map) + 1
            return levels[node]

        for t in self.tasks:
            get_node_level(t["Task"])

        layers = {}
        for node, lvl in levels.items():
            layers.setdefault(lvl, []).append(node)

        pos = {}
        for lvl, nodes in layers.items():
            num_nodes = len(nodes)
            for i, node in enumerate(nodes):
                x = lvl * 2.5
                y = (i - (num_nodes - 1) / 2.0) * 1.8
                pos[node] = np.array([x, y])

        for t_name, preds in predecessors_map.items():
            for p in preds:
                if p in predecessors_map:
                    G.add_edge(p, t_name)

        node_colors = []
        for node in G.nodes():
            if G.nodes[node].get("critical", False):
                node_colors.append("#27AE60")
            else:
                node_colors.append("#2980B9")

        nx.draw_networkx_nodes(G, pos, ax=ax, node_size=2500, node_color=node_colors, alpha=0.95, edgecolors="black", linewidths=1.5)
        
        nx.draw_networkx_edges(
            G, pos, ax=ax, 
            width=2.2, 
            arrowsize=24, 
            arrowstyle="-|>", 
            edge_color="#E74C3C", 
            connectionstyle="arc3,rad=0.1",
            node_size=2500
        )
        
        node_labels = {t["Task"]: f"{t['Task']}\n({t['Duration']}d)" for t in self.tasks}
        nx.draw_networkx_labels(G, pos, labels=node_labels, ax=ax, font_size=10, font_weight="bold", font_color="white")

        proj_title = self.proj_title_entry.get().strip()
        title_str = f"Διάγραμμα Ροής / Δικτύου Δραστηριοτήτων - {proj_title}" if proj_title else "Διάγραμμα Ροής / Δικτύου Δραστηριοτήτων"
        ax.set_title(title_str, fontsize=14, fontweight="bold", pad=20)
        ax.axis("off")
        ax.margins(0.25)
        fig.tight_layout()
        return fig

    def show_network_diagram(self):
        if not self.tasks:
            messagebox.showwarning("Προσοχή", "Δεν υπάρχουν υποέργα για τη δημιουργία διαγράμματος ροής!")
            return

        net_top = tk.Toplevel(self.root)
        net_top.title("Διάγραμμα Ροής & Δικτύου Δραστηριοτήτων (PERT/CPM)")
        net_top.geometry("1200x800")
        net_top.grab_set()

        fig = self.generate_network_figure()

        canvas = FigureCanvasTkAgg(fig, master=net_top)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        btn_close = ttk.Button(net_top, text="Κλείσιμο", command=net_top.destroy)
        btn_close.pack(pady=10)

    def export_network_diagram(self):
        if not self.tasks:
            messagebox.showwarning("Προσοχή", "Δεν υπάρχουν υποέργα για εξαγωγή διαγράμματος ροής!")
            return

        file_path = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG files", "*.png"), ("JPEG files", "*.jpg"), ("All files", "*.*")],
            title="Εξαγωγή Διαγράμματος Ροής/Δικτύου ως Εικόνα"
        )
        if not file_path:
            return

        try:
            fig = self.generate_network_figure()
            fig.savefig(file_path, format="png", dpi=300, bbox_inches='tight', pad_inches=0.2)
            plt.close(fig)
            messagebox.showinfo("Επιτυχία", "Η εξαγωγή του διαγράμματος ροής ολοκληρώθηκε επιτυχώς!")
        except Exception as e:
            messagebox.showerror("Σφάλμα", f"Αποτυχία εξαγωγής διαγράμματος ροής:\n{e}")

    def on_close_application(self):
        if self.tasks or self.holidays:
            response = messagebox.askyesnocancel("Έξοδος από την εφαρμογή", "Θέλετε να αποθηκευτεί το έργο πριν κλείσετε την εφαρμογή;")
            if response is True:
                self.save_project()
                self.root.destroy()
            elif response is False:
                self.root.destroy()
            else:
                return
        else:
            self.root.destroy()

    def toggle_toolbar(self):
        if self.toolbar_visible.get():
            self.file_toolbar_frame.pack(fill=tk.X, padx=10, pady=4, before=self.file_path_label)
        else:
            self.file_toolbar_frame.pack_forget()

    def toggle_zoombar(self):
        if self.zoombar_visible.get():
            self.zoom_toolbar.pack(side=tk.TOP, fill=tk.X, pady=(0, 5), before=self.zoom_toolbar.master.winfo_children()[1] if len(self.zoom_toolbar.master.winfo_children())>1 else None)
        else:
            self.zoom_toolbar.pack_forget()

    def update_zoom_display(self):
        pct = int(round(self.zoom_factor * 100))
        self.zoom_entry_var.set(str(pct))

    def on_zoom_entry_changed(self, event=None):
        try:
            val = int(self.zoom_entry_var.get().strip())
            if val < 20:
                val = 20
            elif val > 300:
                val = 300
            self.zoom_factor = val / 100.0
            self.update_plot()
        except ValueError:
            self.update_zoom_display()

    def zoom_in(self):
        self.zoom_factor = min(3.0, self.zoom_factor + 0.25)
        self.update_zoom_display()
        self.update_plot()

    def zoom_out(self):
        self.zoom_factor = max(0.2, self.zoom_factor - 0.25)
        self.update_zoom_display()
        self.update_plot()

    def zoom_reset(self):
        self.zoom_factor = 1.0
        self.update_zoom_display()
        self.update_plot()

    def toggle_pan(self):
        self.pan_active = not self.pan_active
        if self.pan_active:
            self.pan_btn.state(['pressed'])
            self.plot_canvas.config(cursor="fleur")
        else:
            self.pan_btn.state(['!pressed'])
            self.plot_canvas.config(cursor="")
            self.is_panning = False

    def fit_to_screen(self):
        if not self.tasks:
            return
        
        self.root.update_idletasks()
        canvas_w = self.plot_canvas.winfo_width()
        if canvas_w < 100:
            canvas_w = 900

        schedule_data = self.compute_all_task_dates()
        if not schedule_data:
            return

        min_date = min(v["Start_Date"] for v in schedule_data.values()) - timedelta(days=1)
        max_date = max(v["End_Date"] for v in schedule_data.values()) + timedelta(days=1)
        date_range = pd.date_range(start=min_date, end=max_date)
        days_count = len(date_range)

        if days_count > 0:
            target_fig_width = canvas_w / 100.0 - 0.5
            ideal_width = days_count * 0.35
            if ideal_width > 0:
                self.zoom_factor = max(0.2, min(3.0, target_fig_width / ideal_width))
            else:
                self.zoom_factor = 1.0
                
            self.update_zoom_display()
            self.update_plot()

    def on_plot_frame_configure(self, event):
        self.plot_canvas.configure(scrollregion=self.plot_canvas.bbox("all"))

    def on_canvas_configure(self, event):
        self.plot_canvas.itemconfig(self.plot_canvas_window, minsize=(event.width, event.height))

    def _on_mouse_wheel(self, event):
        try:
            self.plot_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        except:
            pass

    def _on_shift_mouse_wheel(self, event):
        try:
            self.plot_canvas.xview_scroll(int(-1*(event.delta/120)), "units")
        except:
            pass

    def open_multi_pre_popup(self):
        task_names = [t["Task"] for t in self.tasks if t["Task"] != self.selected_item_id]
        if not task_names:
            messagebox.showwarning("Προσοχή", "Δεν υπάρχουν άλλα διαθέσιμα υποέργα για προαπαιτούμενα!")
            return

        top = tk.Toplevel(self.root)
        top.title("Πολλαπλή Επιλογή Προαπαιτούμενων")
        top.geometry("300x350")
        top.grab_set()

        ttk.Label(top, text="Επιλέξτε προαπαιτούμενα υποέργα:", font=("Arial", 10, "bold")).pack(pady=10)

        chk_frame = ttk.Frame(top)
        chk_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        vars_dict = {}
        current_val = self.pre_entry.get().strip()
        current_list = [p.strip() for p in current_val.split(",") if p.strip()]

        for name in task_names:
            var = tk.BooleanVar(value=(name in current_list))
            vars_dict[name] = var
            chk = ttk.Checkbutton(chk_frame, text=f"Υποέργο: {name}", variable=var)
            chk.pack(anchor="w", pady=2)

        def confirm_selection():
            selected = [name for name, var in vars_dict.items() if var.get()]
            self.pre_entry.delete(0, tk.END)
            if not selected:
                self.pre_entry.insert(0, "-")
            else:
                self.pre_entry.insert(0, ", ".join(selected))
            top.destroy()

        btn_confirm = ttk.Button(top, text="Καταχώρηση", command=confirm_selection)
        btn_confirm.pack(pady=15)

    def compute_all_task_dates(self):
        try:
            proj_start_str = self.proj_start_entry.get().strip()
            proj_start_dt = pd.to_datetime(proj_start_str)
        except:
            proj_start_dt = datetime.now()

        holiday_set = set(pd.to_datetime(self.holidays))

        curr = proj_start_dt
        while curr in holiday_set:
            curr += timedelta(days=1)
        proj_start_dt = curr

        task_names = [t["Task"] for t in self.tasks]
        durations = {t["Task"]: t["Duration"] for t in self.tasks}

        predecessors = {}
        for t in self.tasks:
            name = t["Task"]
            raw_pre = t.get("Pre", "-")
            if raw_pre and raw_pre != "-":
                preds = [p.strip() for p in raw_pre.split(",") if p.strip()]
                predecessors[name] = preds
            else:
                predecessors[name] = []

        resolved = {}
        unresolved = set(task_names)
        
        iteration_guard = 0
        while unresolved and iteration_guard < 200:
            iteration_guard += 1
            progress_made = False
            for name in list(unresolved):
                preds = predecessors.get(name, [])
                if all(p in resolved for p in preds):
                    if not preds:
                        start_dt = proj_start_dt
                    else:
                        max_pred_end = max([resolved[p]["End_Date"] for p in preds if p in resolved])
                        start_dt = max_pred_end + timedelta(days=1)
                    
                    while start_dt in holiday_set:
                        start_dt += timedelta(days=1)

                    dur = durations.get(name, 1)
                    curr_dt = start_dt
                    counted_days = 0
                    all_dates = []
                    
                    while counted_days < dur:
                        all_dates.append(curr_dt)
                        if curr_dt not in holiday_set:
                            counted_days += 1
                            if counted_days == dur:
                                break
                        curr_dt += timedelta(days=1)
                    
                    end_dt = curr_dt
                    resolved[name] = {
                        "Start_Date": start_dt,
                        "End_Date": end_dt,
                        "All_Dates": all_dates
                    }
                    unresolved.remove(name)
                    progress_made = True
            if not progress_made:
                for name in list(unresolved):
                    start_dt = proj_start_dt
                    while start_dt in holiday_set:
                        start_dt += timedelta(days=1)
                    dur = durations.get(name, 1)
                    curr_dt = start_dt
                    counted_days = 0
                    all_dates = []
                    while counted_days < dur:
                        all_dates.append(curr_dt)
                        if curr_dt not in holiday_set:
                            counted_days += 1
                            if counted_days == dur:
                                break
                        curr_dt += timedelta(days=1)
                    resolved[name] = {
                        "Start_Date": start_dt,
                        "End_Date": curr_dt,
                        "All_Dates": all_dates
                    }
                    unresolved.remove(name)

        return resolved

    def calculate_cpm_details(self):
        if not self.tasks:
            return {}, {}, {}

        task_names = [t["Task"] for t in self.tasks]
        durations = {t["Task"]: t["Duration"] for t in self.tasks}

        predecessors = {}
        for t in self.tasks:
            name = t["Task"]
            raw_pre = t.get("Pre", "-")
            if raw_pre and raw_pre != "-":
                preds = [p.strip() for p in raw_pre.split(",") if p.strip()]
                predecessors[name] = preds
            else:
                predecessors[name] = []

        successors = {name: [] for name in task_names}
        for t_name, preds in predecessors.items():
            for p in preds:
                if p in successors:
                    successors[p].append(t_name)

        ef = {}
        unresolved = set(task_names)
        resolved = set()
        
        iteration_guard = 0
        while unresolved and iteration_guard < 100:
            iteration_guard += 1
            progress_made = False
            for t_name in list(unresolved):
                preds = predecessors.get(t_name, [])
                if all(p in resolved for p in preds):
                    dur = durations.get(t_name, 1)
                    if not preds:
                        max_prev_ef = 0
                    else:
                        max_prev_ef = max([ef.get(p, 0) for p in preds if p in ef]) if preds else 0
                    ef[t_name] = max_prev_ef + dur
                    resolved.add(t_name)
                    unresolved.remove(t_name)
                    progress_made = True
            if not progress_made:
                for t_name in list(unresolved):
                    ef[t_name] = durations.get(t_name, 1)
                    resolved.add(t_name)
                    unresolved.remove(t_name)

        max_project_ef = max(ef.values()) if ef else 0

        lf = {}
        unresolved_b = set(task_names)
        resolved_b = set()

        iteration_guard = 0
        while unresolved_b and iteration_guard < 100:
            iteration_guard += 1
            progress_made = False
            for t_name in list(unresolved_b):
                succs = successors.get(t_name, [])
                if all(s in resolved_b for s in succs):
                    if not succs:
                        lf[t_name] = max_project_ef
                    else:
                        min_next_lfs = [lf[s] - durations[s] for s in succs if s in lf]
                        lf[t_name] = min(min_next_lfs) if min_next_lfs else max_project_ef
                    resolved_b.add(t_name)
                    unresolved_b.remove(t_name)
                    progress_made = True
            if not progress_made:
                for t_name in list(unresolved_b):
                    lf[t_name] = max_project_ef
                    resolved_b.add(t_name)
                    unresolved_b.remove(t_name)

        slack_dict = {}
        for t_name in task_names:
            slack = lf.get(t_name, max_project_ef) - ef.get(t_name, max_project_ef)
            slack_dict[t_name] = max(0, int(round(slack)))

        return ef, lf, slack_dict

    def check_and_update_day_buttons(self):
        for day_num in range(7):
            self.day_vars[day_num].set(False)
            self.day_buttons[day_num].config(fg="black")

        if not self.tasks:
            return

        schedule_data = self.compute_all_task_dates()
        if not schedule_data:
            return

        min_date = min(v["Start_Date"] for v in schedule_data.values())
        max_date = max(v["End_Date"] for v in schedule_data.values())
        full_range = pd.date_range(start=min_date, end=max_date)

        if len(full_range) == 0:
            return

        holiday_set = set(pd.to_datetime(self.holidays))

        for day_num in range(7):
            days_in_range = [d for d in full_range if d.weekday() == day_num]
            if not days_in_range:
                continue
            
            all_are_holidays = all(d in holiday_set for d in days_in_range)
            if all_are_holidays:
                self.day_vars[day_num].set(True)
                self.day_buttons[day_num].config(fg="red", selectcolor="#FFF1A5")

    def on_day_button_toggle(self, day_num):
        self.toggle_day_holidays(day_num)

    def sort_holidays_column(self, col):
        if self.hol_sort_col == col:
            self.hol_sort_reverse = not self.hol_sort_reverse
        else:
            self.hol_sort_col = col
            self.hol_sort_reverse = False

        data_list = [(self.hol_tree.set(child, col), child) for child in self.hol_tree.get_children('')]
        
        if col == "Date":
            data_list.sort(key=lambda x: datetime.strptime(x[0], "%Y-%m-%d"), reverse=self.hol_sort_reverse)
        else:
            data_list.sort(key=lambda x: x[0], reverse=self.hol_sort_reverse)

        for index, (val, child) in enumerate(data_list):
            self.hol_tree.move(child, '', index)

        day_text = "Ημέρα 🔽" if col == "Day" and self.hol_sort_reverse else ("Ημέρα 🔼" if col == "Day" else "Ημέρα ↕")
        date_text = "Ημερομηνία 🔽" if col == "Date" and self.hol_sort_reverse else ("Ημερομηνία 🔼" if col == "Date" else "Ημερομηνία ↕")
        
        self.hol_tree.heading("Day", text=day_text)
        self.hol_tree.heading("Date", text=date_text)

    def toggle_day_holidays(self, day_num):
        if not self.tasks:
            self.day_vars[day_num].set(False)
            self.day_buttons[day_num].config(fg="black")
            messagebox.showwarning("Προσοχή", "Προσθέστε πρώτα υποέργα στο έργο!")
            return

        is_pressed = self.day_vars[day_num].get()

        try:
            min_dt = pd.to_datetime(self.proj_start_entry.get().strip())
        except:
            min_dt = pd.to_datetime("2026-10-19")

        schedule_data = self.compute_all_task_dates()
        max_end_dt = max([v["End_Date"] for v in schedule_data.values()]) + timedelta(days=7) if schedule_data else min_dt + timedelta(days=30)
        
        date_range = pd.date_range(start=min_dt, end=max_end_dt)

        if is_pressed:
            for d in date_range:
                if d.weekday() == day_num:
                    h_str = d.strftime("%Y-%m-%d")
                    if h_str not in self.holidays:
                        self.holidays.append(h_str)
        else:
            holidays_to_remove = []
            for h_str in self.holidays:
                try:
                    dt = datetime.strptime(h_str, "%Y-%m-%d")
                    if dt.weekday() == day_num:
                        holidays_to_remove.append(h_str)
                except ValueError:
                    continue

            for h_str in holidays_to_remove:
                if h_str in self.holidays:
                    self.holidays.remove(h_str)

        self.deleted_holidays_stack.clear()
        self.undo_hol_btn.config(state=tk.DISABLED)
        
        self.update_holidays_tree()
        self.update_tree()
        self.update_plot()
        self.check_and_update_day_buttons()

    def remove_single_holiday(self, h_str):
        if h_str in self.holidays:
            idx = self.holidays.index(h_str)
            tasks_snapshot = [t.copy() for t in self.tasks]
            self.deleted_holidays_stack.append((h_str, idx, tasks_snapshot))
            self.undo_hol_btn.config(state=tk.NORMAL)
            
            self.holidays.remove(h_str)

            self.update_holidays_tree()
            self.update_tree()
            self.update_plot()
            self.check_and_update_day_buttons()

    def open_proj_calendar_popup(self):
        top = tk.Toplevel(self.root)
        top.title("Επιλογή Ημερομηνίας Έναρξης Έργου")
        
        window_width = 320
        window_height = 300
        screen_height = self.root.winfo_screenheight()
        
        x = 50
        y = screen_height - window_height - 100
        
        top.geometry(f"{window_width}x{window_height}+{x}+{y}")
        top.grab_set()

        try:
            curr_val = self.proj_start_entry.get().strip()
            parts = [int(p) for p in curr_val.split("-")]
            y_val, m_val, d_val = parts[0], parts[1], parts[2]
        except:
            y_val, m_val, d_val = 2026, 10, 19

        cal = Calendar(top, selectmode='day', year=y_val, month=m_val, day=d_val, date_pattern='yyyy-mm-dd')
        cal.pack(pady=15, fill=tk.BOTH, expand=True)

        def confirm_date():
            selected_date = cal.get_date()
            top.destroy()
            self.proj_start_entry.delete(0, tk.END)
            self.proj_start_entry.insert(0, selected_date)
            self.update_tree()
            self.update_plot()

        btn_confirm = ttk.Button(top, text="Καταχώρηση Ημερομηνίας", command=confirm_date)
        btn_confirm.pack(pady=10)

    def open_calendar_popup(self):
        top = tk.Toplevel(self.root)
        top.title("Επιλογή Ημερομηνίας Αργίας")
        
        window_width = 320
        window_height = 300
        screen_height = self.root.winfo_screenheight()
        
        x = 50
        y = screen_height - window_height - 100
        
        top.geometry(f"{window_width}x{window_height}+{x}+{y}")
        top.grab_set()

        cal = Calendar(top, selectmode='day', year=2026, month=10, day=19, date_pattern='yyyy-mm-dd')
        cal.pack(pady=15, fill=tk.BOTH, expand=True)

        def confirm_date():
            selected_date = cal.get_date()
            top.destroy()
            self.add_holiday_from_calendar(selected_date)

        btn_confirm = ttk.Button(top, text="Καταχώρηση Αργίας", command=confirm_date)
        btn_confirm.pack(pady=10)

    def open_holiday_range_popup(self):
        top = tk.Toplevel(self.root)
        top.title("Προσθήκη Εύρους Αργιών (Season)")
        top.geometry("300x230")
        top.grab_set()

        ttk.Label(top, text="Από Ημερομηνία:", font=("Arial", 9, "bold")).pack(anchor="w", padx=20, pady=(15, 2))
        start_frame = ttk.Frame(top)
        start_frame.pack(anchor="w", padx=20, pady=2)

        start_entry = ttk.Entry(start_frame, width=15)
        start_entry.pack(side=tk.LEFT, padx=(0, 5))
        start_entry.insert(0, datetime.now().strftime("%Y-%m-%d"))

        def pick_start_date():
            sub_top = tk.Toplevel(top)
            sub_top.title("Επιλογή 'Από'")
            sub_top.geometry("320x300")
            sub_top.grab_set()
            try:
                curr = start_entry.get().strip()
                p = [int(x) for x in curr.split("-")]
                y_v, m_v, d_v = p[0], p[1], p[2]
            except:
                y_v, m_v, d_v = 2026, 10, 19
            cal = Calendar(sub_top, selectmode='day', year=y_v, month=m_v, day=d_v, date_pattern='yyyy-mm-dd')
            cal.pack(pady=15, fill=tk.BOTH, expand=True)
            def set_d():
                start_entry.delete(0, tk.END)
                start_entry.insert(0, cal.get_date())
                sub_top.destroy()
            ttk.Button(sub_top, text="Επιλογή", command=set_d).pack(pady=10)

        ttk.Button(start_frame, text="📅", width=4, command=pick_start_date).pack(side=tk.LEFT)

        ttk.Label(top, text="Μέχρι Ημερομηνία:", font=("Arial", 9, "bold")).pack(anchor="w", padx=20, pady=(10, 2))
        end_frame = ttk.Frame(top)
        end_frame.pack(anchor="w", padx=20, pady=2)

        end_entry = ttk.Entry(end_frame, width=15)
        end_entry.pack(side=tk.LEFT, padx=(0, 5))
        end_entry.insert(0, datetime.now().strftime("%Y-%m-%d"))

        def pick_end_date():
            sub_top = tk.Toplevel(top)
            sub_top.title("Επιλογή 'Μέχρι'")
            sub_top.geometry("320x300")
            sub_top.grab_set()
            try:
                curr = end_entry.get().strip()
                p = [int(x) for x in curr.split("-")]
                y_v, m_v, d_v = p[0], p[1], p[2]
            except:
                y_v, m_v, d_v = 2026, 10, 19
            cal = Calendar(sub_top, selectmode='day', year=y_v, month=m_v, day=d_v, date_pattern='yyyy-mm-dd')
            cal.pack(pady=15, fill=tk.BOTH, expand=True)
            def set_d():
                end_entry.delete(0, tk.END)
                end_entry.insert(0, cal.get_date())
                sub_top.destroy()
            ttk.Button(sub_top, text="Επιλογή", command=set_d).pack(pady=10)

        ttk.Button(end_frame, text="📅", width=4, command=pick_end_date).pack(side=tk.LEFT)

        def confirm_range():
            start_str = start_entry.get().strip()
            end_str = end_entry.get().strip()
            try:
                start_dt = pd.to_datetime(start_str)
                end_dt = pd.to_datetime(end_str)
                if start_dt > end_dt:
                    messagebox.showerror("Σφάλμα", "Η ημερομηνία 'Από' δεν μπορεί να είναι μεταγενέστερη της 'Μέχρι'!")
                    return
                
                date_range = pd.date_range(start=start_dt, end=end_dt)
                added_count = 0
                for d in date_range:
                    h_str = d.strftime("%Y-%m-%d")
                    if h_str not in self.holidays:
                        self.holidays.append(h_str)
                        added_count += 1
                
                if added_count > 0:
                    self.deleted_holidays_stack.clear()
                    self.undo_hol_btn.config(state=tk.DISABLED)
                    self.update_holidays_tree()
                    self.update_tree()
                    self.update_plot()
                    self.check_and_update_day_buttons()
                
                top.destroy()
            except Exception as e:
                messagebox.showerror("Σφάλμα", f"Λανθασμένη μορφή ημερομηνιών!\n{e}")

        ttk.Button(top, text="Καταχώρηση Season", command=confirm_range).pack(pady=15)

    def add_holiday_from_calendar(self, h_str):
        if h_str in self.holidays:
            return

        self.holidays.append(h_str)

        self.deleted_holidays_stack.clear()
        self.undo_hol_btn.config(state=tk.DISABLED)
        self.update_holidays_tree()
        self.update_tree()
        self.update_plot()
        self.check_and_update_day_buttons()

    def update_file_label(self):
        if self.current_file_path:
            self.file_path_label.config(text=f"Αρχείο: {self.current_file_path}")
        else:
            self.file_path_label.config(text="Αρχείο: [ Κανένα / Νέο Έργο ]")

    def update_tree(self, selected_task_name=None):
        for item in self.tree.get_children():
            self.tree.delete(item)
            
        schedule_data = self.compute_all_task_dates()
        ef_map, lf_map, slack_map = self.calculate_cpm_details()

        critical_tasks = []

        for t in self.tasks:
            t_name = t["Task"]
            t_title = t.get("Title", "")
            s_info = schedule_data.get(t_name, {})
            start_str = s_info.get("Start_Date", pd.to_datetime("2026-10-19")).strftime("%Y-%m-%d")
            end_str = s_info.get("End_Date", pd.to_datetime("2026-10-19")).strftime("%Y-%m-%d")
            
            pre_val = t.get("Pre", "-")
            if not pre_val:
                pre_val = "-"
            ef_val = ef_map.get(t_name, 0)
            lf_val = lf_map.get(t_name, 0)
            slack_val = slack_map.get(t_name, 0)
            
            if slack_val == 0:
                critical_tasks.append(t_name)

            item_id = self.tree.insert("", tk.END, values=(
                t_name, t_title, pre_val, start_str, end_str, f"{t['Duration']}", ef_val, lf_val, slack_val
            ))
            
            if selected_task_name and t_name == selected_task_name:
                self.tree.selection_set(item_id)
                self.tree.focus(item_id)

        if critical_tasks:
            self.val_cpm_path.config(text=" - ".join(critical_tasks))
        else:
            self.val_cpm_path.config(text="-")

        self.update_project_summary()
        self.check_and_update_day_buttons()

    def update_project_summary(self):
        if not self.tasks:
            self.val_no_holidays.config(text="0 ημέρες")
            self.val_holidays_count.config(text="0 ημέρες")
            self.val_with_holidays.config(text="0 ημέρες")
            return

        schedule_data = self.compute_all_task_dates()
        working_dates = set()
        holiday_dates_set = set(pd.to_datetime(self.holidays))

        for t_name, info in schedule_data.items():
            for d in info["All_Dates"]:
                if d not in holiday_dates_set:
                    working_dates.add(d)

        clean_duration = len(working_dates)

        if not working_dates:
            self.val_no_holidays.config(text="0 ημέρες")
            self.val_holidays_count.config(text="0 ημέρες")
            self.val_with_holidays.config(text="0 ημέρες")
            return

        min_date = min(working_dates)
        max_date = max(working_dates)

        project_date_range = pd.date_range(start=min_date, end=max_date)
        holidays_in_project = sum(1 for d in project_date_range if d in holiday_dates_set)
        total_duration = clean_duration + holidays_in_project

        self.val_no_holidays.config(text=f"{clean_duration} ημέρες")
        self.val_holidays_count.config(text=f"{holidays_in_project} ημέρες")
        self.val_with_holidays.config(text=f"{total_duration} ημέρες")

    def update_holidays_tree(self):
        for item in self.hol_tree.get_children():
            self.hol_tree.delete(item)

        days_gr = {0: "Δευτέρα", 1: "Τρίτη", 2: "Τετάρτη", 3: "Πέμπτη", 4: "Παρασκευή", 5: "Σάββατο", 6: "Κυριακή"}

        hol_data = []
        for h in self.holidays:
            try:
                dt = datetime.strptime(h, "%Y-%m-%d")
                day_name = days_gr[dt.weekday()]
            except ValueError:
                day_name = "Άγνωστη"
                dt = datetime.min
            hol_data.append((day_name, h, dt))

        if self.hol_sort_col == "Date":
            hol_data.sort(key=lambda x: x[2], reverse=self.hol_sort_reverse)
        elif self.hol_sort_col == "Day":
            hol_data.sort(key=lambda x: x[0], reverse=self.hol_sort_reverse)

        for day_name, h, _ in hol_data:
            self.hol_tree.insert("", tk.END, values=(day_name, h))

    def move_task(self, direction):
        selected_item = self.tree.selection()
        if not selected_item:
            messagebox.showwarning("Προσοχή", "Επιλέξτε ένα υποέργο από τη λίστα για να το μετακινήσετε.")
            return

        item_values = self.tree.item(selected_item, "values")
        task_name = item_values[0]

        current_idx = -1
        for i, t in enumerate(self.tasks):
            if t["Task"] == task_name:
                current_idx = i
                break

        if current_idx == -1:
            return

        new_idx = current_idx + direction

        if new_idx < 0 or new_idx >= len(self.tasks):
            return

        task_obj = self.tasks.pop(current_idx)
        self.tasks.insert(new_idx, task_obj)

        self.update_tree(selected_task_name=task_name)
        self.update_plot()

        children = self.tree.get_children()
        for idx, item in enumerate(children):
            vals = self.tree.item(item, "values")
            if vals and vals[0] == task_name:
                total_items = len(children)
                if total_items > 0:
                    fraction = idx / float(total_items)
                    self.tree.yview_moveto(fraction)
                break

    def save_project(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Αποθήκευση Έργου"
        )
        if not file_path:
            return

        data = {
            "project_title": self.proj_title_entry.get().strip(),
            "project_start": self.proj_start_entry.get().strip(),
            "tasks": self.tasks,
            "holidays": self.holidays
        }
        try:
            with open(file_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=4)
            self.current_file_path = file_path
            self.update_file_label()
            messagebox.showinfo("Επιτυχία", "Το έργο αποθηκεύτηκε επιτυχώς!")
        except Exception as e:
            messagebox.showerror("Σφάλμα", f"Αποτυχία αποθήκευσης αρχείου:\n{e}")

    def export_to_xml(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".xml",
            filetypes=[("XML files", "*.xml"), ("All files", "*.*")],
            title="Εξαγωγή Δεδομένων σε XML"
        )
        if not file_path:
            return

        try:
            root_elem = ET.Element("Project")
            
            title_elem = ET.SubElement(root_elem, "Title")
            title_elem.text = self.proj_title_entry.get().strip()

            start_elem = ET.SubElement(root_elem, "StartDate")
            start_elem.text = self.proj_start_entry.get().strip()

            tasks_elem = ET.SubElement(root_elem, "Tasks")
            for t in self.tasks:
                task_elem = ET.SubElement(tasks_elem, "Task")
                
                t_id = ET.SubElement(task_elem, "Id")
                t_id.text = str(t.get("Task", ""))

                t_title = ET.SubElement(task_elem, "TaskTitle")
                t_title.text = str(t.get("Title", ""))

                t_pre = ET.SubElement(task_elem, "Predecessors")
                t_pre.text = str(t.get("Pre", "-"))

                t_dur = ET.SubElement(task_elem, "Duration")
                t_dur.text = str(t.get("Duration", 1))

            holidays_elem = ET.SubElement(root_elem, "Holidays")
            for h in self.holidays:
                hol_elem = ET.SubElement(holidays_elem, "Holiday")
                hol_elem.text = str(h)

            rough_string = ET.tostring(root_elem, encoding="utf-8")
            reparsed = xml.dom.minidom.parseString(rough_string)
            pretty_xml = reparsed.toprettyxml(indent="    ", encoding="utf-8")

            with open(file_path, "wb") as f:
                f.write(pretty_xml)

            messagebox.showinfo("Επιτυχία", "Η εξαγωγή σε XML ολοκληρώθηκε επιτυχώς!")
        except Exception as e:
            messagebox.showerror("Σφάλμα", f"Αποτυχία εξαγωγής σε XML:\n{e}")

    def load_project(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Άνοιγμα Έργου"
        )
        if not file_path:
            return

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            
            if "tasks" in data and "holidays" in data:
                self.tasks = []
                for t in data["tasks"]:
                    self.tasks.append({
                        "Task": t["Task"],
                        "Title": t.get("Title", ""),
                        "Pre": t.get("Pre", "-"),
                        "Duration": t["Duration"]
                    })
                
                self.holidays = data["holidays"]
                self.hol_sort_col = "Date"
                self.hol_sort_reverse = False
                self.hol_tree.heading("Date", text="Ημερομηνία 🔽")
                self.hol_tree.heading("Day", text="Ημέρα ↕")
                
                if "project_title" in data:
                    self.proj_title_entry.delete(0, tk.END)
                    self.proj_title_entry.insert(0, data["project_title"])

                if "project_start" in data and data["project_start"]:
                    self.proj_start_entry.delete(0, tk.END)
                    self.proj_start_entry.insert(0, data["project_start"])

                self.current_file_path = file_path
                self.deleted_holidays_stack.clear()
                self.deleted_tasks_stack.clear()
                self.form_history_stack.clear()
                self.undo_hol_btn.config(state=tk.DISABLED)
                self.undo_task_btn.config(state=tk.DISABLED)
                self.undo_form_btn.config(state=tk.DISABLED)
                self.update_file_label()
                self.clear_form()

                self.update_tree()
                self.update_holidays_tree()
                self.update_plot()
                self.check_and_update_day_buttons()
                
                # Αυτόματη προσαρμογή στο άνοιγμα έργου
                self.root.after(100, self.fit_to_screen)
                
                messagebox.showinfo("Επιτυχία", "Το έργο φορτώθηκε επιτυχώς!")
            else:
                messagebox.showerror("Σφάλμα", "Το αρχείο δεν έχει τη σωστή δομή δεδομένων!")
        except Exception as e:
            messagebox.showerror("Σφάλμα", f"Αποτυχία ανάγνωσης αρχείου:\n{e}")

    def export_to_pdf(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf"), ("All files", "*.*")],
            title="Εκτύπωση σε PDF (Landscape A4)"
        )
        if not file_path:
            return

        try:
            self.fig.savefig(file_path, format="pdf", orientation="landscape", dpi=300, bbox_inches='tight', pad_inches=0.1)
            messagebox.showinfo("Επιτυχία", "Η εκτύπωση σε PDF ολοκληρώθηκε επιτυχώς!")
        except Exception as e:
            messagebox.showerror("Σφάλμα", f"Αποτυχία δημιουργίας PDF:\n{e}")

    def delete_holiday(self):
        selected_item = self.hol_tree.selection()
        if not selected_item:
            messagebox.showwarning("Προσοχή", "Επιλέξτε μια αργία από τη λίστα για να τη διαγράψετε.")
            return

        item_values = self.hol_tree.item(selected_item, "values")
        h_str = item_values[1]

        self.remove_single_holiday(h_str)

    def undo_delete_holiday(self):
        if self.deleted_holidays_stack:
            date_val, idx, tasks_snapshot = self.deleted_holidays_stack.pop()
            
            if date_val not in self.holidays:
                self.holidays.insert(idx, date_val)
            
            self.tasks = tasks_snapshot
            
            if not self.deleted_holidays_stack:
                self.undo_hol_btn.config(state=tk.DISABLED)

            self.update_holidays_tree()
            self.update_tree()
            self.update_plot()
            self.check_and_update_day_buttons()

    def delete_task(self):
        selected_item = self.tree.selection()
        if not selected_item:
            messagebox.showwarning("Προσοχή", "Επιλέξτε ένα υποέργο από τη λίστα για να το διαγράψετε.")
            return

        item_values = self.tree.item(selected_item, "values")
        task_name = item_values[0]

        task_obj = None
        idx = -1
        for i, t in enumerate(self.tasks):
            if t["Task"] == task_name:
                task_obj = t.copy()
                idx = i
                break

        if task_obj is not None:
            self.deleted_tasks_stack.append((task_obj, idx))
            self.undo_task_btn.config(state=tk.NORMAL)
            
            self.tasks.pop(idx)
            self.clear_form()
            self.update_tree()
            self.update_plot()
            self.check_and_update_day_buttons()

    def undo_delete_task(self):
        if self.deleted_tasks_stack:
            task_obj, idx = self.deleted_tasks_stack.pop()
            if not any(t["Task"] == task_obj["Task"] for t in self.tasks):
                self.tasks.insert(idx, task_obj)
            
            if not self.deleted_tasks_stack:
                self.undo_task_btn.config(state=tk.DISABLED)

            self.clear_form()
            self.update_tree()
            self.update_plot()
            self.check_and_update_day_buttons()

    def prepare_edit(self, event):
        selected_items = self.tree.selection()
        if not selected_items:
            return
        
        item = selected_items[0]
        values = self.tree.item(item, "values")
        
        task_name = values[0]
        for t in self.tasks:
            if t["Task"] == task_name:
                self.selected_item_id = task_name
                self.task_entry.delete(0, tk.END)
                self.task_entry.insert(0, t["Task"])
                
                self.title_entry.delete(0, tk.END)
                self.title_entry.insert(0, t.get("Title", ""))
                
                self.pre_entry.delete(0, tk.END)
                pre_val = t.get("Pre", "-")
                if not pre_val:
                    pre_val = "-"
                self.pre_entry.insert(0, pre_val)

                self.duration_entry.delete(0, tk.END)
                self.duration_entry.insert(0, str(t["Duration"]))
                break

        self.save_btn.config(text="Update")
        self.undo_form_btn.config(state=tk.DISABLED)

    def clear_form(self):
        self.selected_item_id = None
        self.task_entry.delete(0, tk.END)
        self.title_entry.delete(0, tk.END)
        self.pre_entry.delete(0, tk.END)
        self.pre_entry.insert(0, "-")
        self.duration_entry.delete(0, tk.END)
        self.save_btn.config(text="Προσθήκη Υποέργου")
        self.undo_form_btn.config(state=tk.DISABLED)
        if self.tree.selection():
            self.tree.selection_remove(self.tree.selection())

    def save_task(self):
        name = self.task_entry.get().strip()
        title = self.title_entry.get().strip()
        pre = self.pre_entry.get().strip()
        dur_str = self.duration_entry.get().strip()

        if not name or not dur_str:
            messagebox.showerror("Σφάλμα", "Παρακαλώ συμπληρώστε τα υποχρεωτικά πεδία (Υποέργο, Διάρκεια)!")
            return

        try:
            duration = int(dur_str)
            if duration <= 0:
                raise ValueError()
        except ValueError:
            messagebox.showerror("Σφάλμα", "Λανθασμένα στοιχεία!\nΗ διάρκεια πρέπει να είναι θετικός ακέραιος αριθμός.")
            return

        tasks_snapshot = [t.copy() for t in self.tasks]
        selected_snapshot = self.selected_item_id

        if self.selected_item_id is None:
            if any(t["Task"] == name for t in self.tasks):
                messagebox.showerror("Σφάλμα", "Υπάρχει ήδη υποέργο με αυτό το όνομα!")
                return
            self.tasks.append({"Task": name, "Title": title, "Pre": pre, "Duration": duration})
        else:
            for t in self.tasks:
                if t["Task"] == self.selected_item_id:
                    t["Task"] = name
                    t["Title"] = title
                    t["Pre"] = pre
                    t["Duration"] = duration
                    break
            self.clear_form()

        self.form_history_stack.append((tasks_snapshot, selected_snapshot))
        self.undo_form_btn.config(state=tk.NORMAL)

        self.update_tree()
        self.update_plot()
        self.check_and_update_day_buttons()
        if self.selected_item_id is None:
            self.task_entry.delete(0, tk.END)
            self.title_entry.delete(0, tk.END)
            self.pre_entry.delete(0, tk.END)
            self.pre_entry.insert(0, "-")
            self.duration_entry.delete(0, tk.END)

    def undo_form_action(self):
        if self.form_history_stack:
            tasks_snapshot, _ = self.form_history_stack.pop()
            self.tasks = tasks_snapshot
            self.clear_form()
            
            if not self.form_history_stack:
                self.undo_form_btn.config(state=tk.DISABLED)

            self.update_tree()
            self.update_plot()
            self.check_and_update_day_buttons()

    def open_help_window(self):
        help_top = tk.Toplevel(self.root)
        help_top.title("Βοήθεια & Οδηγίες Χρήσης - Διάγραμμα Gantt")
        help_top.geometry("720x650")
        help_top.grab_set()

        text_frame = ttk.Frame(help_top)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)

        text_scroll = ttk.Scrollbar(text_frame, orient=tk.VERTICAL)
        
        help_text = tk.Text(
            text_frame, 
            wrap=tk.WORD, 
            yscrollcommand=text_scroll.set,
            font=("Arial", 11),
            padx=12,
            pady=12,
            background="#FDFEFE"
        )
        text_scroll.config(command=help_text.yview)
        
        text_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        help_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        help_text.tag_config("heading", font=("Arial", 12, "bold"), foreground="#1B4F72", spacing1=10, spacing2=4)
        help_text.tag_config("prefix_bold", font=("Arial", 11, "bold"), foreground="#000000")
        help_text.tag_config("body", font=("Arial", 11), spacing1=2, spacing2=2)

        help_text.insert(tk.END, "📌 ΕΙΣΑΓΩΓΗ & ΣΚΟΠΟΣ ΛΟΓΙΣΜΙΚΟΥ\n", "heading")
        help_text.insert(tk.END, "Σκοπός Λογισμικού: ", "prefix_bold")
        help_text.insert(tk.END, "Το πρόγραμμα αυτό είναι ένα εργαλείο διαχείρισης έργου (Project Management) που δημιουργεί αυτόματα Διαγράμματα Gantt και υπολογίζει το Critical Path (Κρίσιμη Διαδρομή).\n\n", "body")

        help_text.insert(tk.END, "🚀 ΠΩΣ ΞΕΚΙΝΑ Η ΚΑΤΑΧΩΡΗΣΗ ΕΡΓΟΥ\n", "heading")
        help_text.insert(tk.END, "1. Τίτλος & Έναρξη Έργου: ", "prefix_bold")
        help_text.insert(tk.END, "Ορίζετε τον τίτλο και την ημερομηνία έναρξης του έργου στα αντίστοιχα πεδία.\n", "body")
        
        help_text.insert(tk.END, "2. Στοιχεία Υποέργου: ", "prefix_bold")
        help_text.insert(tk.END, "Στην ενότητα Υποέργο συμπληρώνετε τον κωδικό, προαιρετικά τίτλο, διάρκεια και προαπαιτούμενα.\n\n", "body")

        help_text.insert(tk.END, "📄 ΕΞΑΓΩΓΗ ΔΕΔΟΜΕΝΩΝ & ΔΙΑΓΡΑΜΜΑ ΡΟΗΣ\n", "heading")
        help_text.insert(tk.END, "Εξαγωγή XML & Εικόνας Δικτύου: ", "prefix_bold")
        help_text.insert(tk.END, "Μπορείτε να εξαγάγετε τα δεδομένα σε XML ή το διάγραμμα ροής/δικτύου ως εικόνα (PNG) μέσω του μενού File.\n", "body")
        help_text.insert(tk.END, "Διάγραμμα Ροής/Δικτύου: ", "prefix_bold")
        help_text.insert(tk.END, "Με το κουμπί 🔀 ή μέσω του μενού View -> Show Flow/Network Diagram, η εφαρμογή κατασκευάζει αυτόματα το δίκτυο δραστηριοτήτων (PERT/CPM) με ιεραρχική διάταξη.\n\n", "body")

        help_text.config(state=tk.DISABLED)

        btn_close = ttk.Button(help_top, text="Κλείσιμο", command=help_top.destroy)
        btn_close.pack(pady=10)

    def open_about_window(self):
        about_top = tk.Toplevel(self.root)
        about_top.title("About - Διάγραμμα Gantt")
        about_top.geometry("380x250")
        about_top.grab_set()

        about_frame = ttk.Frame(about_top)
        about_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)

        ttk.Label(about_frame, text="Τίτλος λογισμικού: Διάγραμμα Gantt", font=("Arial", 11, "bold")).pack(anchor="w", pady=4)
        ttk.Label(about_frame, text="Έτος δημιουργίας: 2026", font=("Arial", 11)).pack(anchor="w", pady=4)
        ttk.Label(about_frame, text="Έκδοση του Λογισμικού: Version 1.0", font=("Arial", 11)).pack(anchor="w", pady=4)
        ttk.Label(about_frame, text="Συντάκτης: Αντώνης Κατσούλης", font=("Arial", 11)).pack(anchor="w", pady=4)

        btn_close = ttk.Button(about_top, text="Κλείσιμο", command=about_top.destroy)
        btn_close.pack(pady=10)

    def on_plot_click(self, event):
        if self.pan_active or event.button != 1:
            return

        if event.xdata is None or event.ydata is None:
            return

        clicked_task = None
        for task_name, y_val, x_min, x_max in self.task_rects:
            if (y_val - 0.35 <= event.ydata <= y_val + 0.35) and (x_min <= event.xdata <= x_max):
                clicked_task = task_name
                break

        if clicked_task:
            children = self.tree.get_children()
            for idx, item in enumerate(children):
                values = self.tree.item(item, "values")
                if values and values[0] == clicked_task:
                    self.tree.selection_set(item)
                    self.tree.focus(item)
                    
                    total_items = len(children)
                    if total_items > 0:
                        fraction = idx / float(total_items)
                        self.tree.yview_moveto(fraction)
                    return

        clicked_holiday = None
        for h_date, x_min, x_max in self.holiday_rects:
            if x_min <= event.xdata <= x_max:
                clicked_holiday = h_date
                break

        if clicked_holiday:
            children = self.hol_tree.get_children()
            for idx, item in enumerate(children):
                h_values = self.hol_tree.item(item, "values")
                if h_values and h_values[1] == clicked_holiday:
                    self.hol_tree.selection_set(item)
                    self.hol_tree.focus(item)
                    
                    self.hol_tree.see(item)
                    return

    def on_press(self, event):
        if self.pan_active and event.button == 1 and event.x is not None and event.y is not None:
            self.is_panning = True
            self.pan_start_x = event.x
            self.pan_start_y = event.y

    def on_motion(self, event):
        if self.pan_active and self.is_panning and event.x is not None and event.y is not None:
            dx = event.x - self.pan_start_x
            dy = event.y - self.pan_start_y
            
            self.pan_start_x = event.x
            self.pan_start_y = event.y
            
            current_x = self.plot_canvas.xview()
            current_y = self.plot_canvas.yview()
            
            scroll_region = self.plot_canvas.bbox("all")
            if scroll_region:
                total_w = scroll_region[2] - scroll_region[0]
                total_h = scroll_region[3] - scroll_region[1]
                
                if total_w > 0 and total_h > 0:
                    new_x = current_x[0] - (dx / total_w)
                    new_y = current_y[0] - (dy / total_h)
                    
                    self.plot_canvas.xview_moveto(max(0.0, min(1.0, new_x)))
                    self.plot_canvas.yview_moveto(max(0.0, min(1.0, new_y)))
                    self.plot_canvas.update_idletasks()

    def on_release(self, event):
        if event.button == 1:
            self.is_panning = False

    def update_plot(self):
        for widget in self.plot_frame.winfo_children():
            widget.destroy()

        self.task_rects = []
        self.holiday_rects = []

        if not self.tasks:
            self.fig, self.ax = plt.subplots(figsize=(9, 5.5))
            self.ax.text(0.5, 0.5, "Δεν υπάρχουν ενεργά υποέργα", 
                    horizontalalignment='center', verticalalignment='center', fontsize=12)
            self.ax.axis('off')
        else:
            schedule_data = self.compute_all_task_dates()
            _, _, slack_map = self.calculate_cpm_details()

            processed_tasks = []
            for t in self.tasks:
                t_name = t["Task"]
                s_info = schedule_data.get(t_name, {})
                s_dt = s_info.get("Start_Date", pd.to_datetime("2026-10-19"))
                e_dt = s_info.get("End_Date", pd.to_datetime("2026-10-19"))
                all_d = s_info.get("All_Dates", [s_dt])
                
                is_critical = (slack_map.get(t_name, 0) == 0)
                processed_tasks.append({
                    "Task": t_name,
                    "Title": t.get("Title", ""),
                    "Start_Date": s_dt,
                    "End_Date": e_dt,
                    "All_Dates": all_d,
                    "Duration": t["Duration"],
                    "Is_Critical": is_critical,
                    "Pre": t.get("Pre", "-")
                })

            df = pd.DataFrame(processed_tasks)
            task_list = [t["Task"] for t in self.tasks]
            
            min_date = df["Start_Date"].min() - timedelta(days=1)
            max_date = df["End_Date"].max() + timedelta(days=1)
            
            date_range = pd.date_range(start=min_date, end=max_date)
            num_tasks = len(task_list)

            fig_width = max(9.0, len(date_range) * 0.35 * self.zoom_factor)
            fig_height = max(5.5, num_tasks * 0.6 + 2.5)

            self.fig, self.ax = plt.subplots(figsize=(fig_width, fig_height))

            holiday_dates_set = set(pd.to_datetime(self.holidays))

            def is_holiday(dt):
                return dt in holiday_dates_set

            for idx, d in enumerate(date_range):
                if is_holiday(d): 
                    self.ax.axvspan(idx - 0.5, idx + 0.5, color='#FFF1A5', zorder=0)
                    self.holiday_rects.append((d.strftime("%Y-%m-%d"), idx - 0.5, idx + 0.5))

            for _, row in df.iterrows():
                t_name = row["Task"]
                y_idx = num_tasks - 1 - task_list.index(t_name)
                is_crit = row["Is_Critical"]
                bar_color = "#27AE60" if is_crit else "#2980B9"
                
                start_d_item = row["All_Dates"][0]
                end_d_item = row["All_Dates"][-1]
                
                s_matches = np.where(date_range == start_d_item)[0]
                e_matches = np.where(date_range == end_d_item)[0]
                
                if len(s_matches) > 0 and len(e_matches) > 0:
                    s_idx = s_matches[0]
                    e_idx = e_matches[0]
                    self.task_rects.append((t_name, y_idx, s_idx - 0.5, e_idx + 0.5))

                for d_item in row["All_Dates"]:
                    if d_item in date_range:
                        d_idx = np.where(date_range == d_item)[0][0]
                        if not is_holiday(d_item):
                            self.ax.barh(y_idx, 1.0, left=d_idx - 0.5, color="white", edgecolor=bar_color, height=0.6, hatch='///////', alpha=1.0, zorder=2)

            for _, row in df.iterrows():
                t_name = row["Task"]
                y_idx = num_tasks - 1 - task_list.index(t_name)
                is_crit = row["Is_Critical"]
                bar_color = "#27AE60" if is_crit else "#2980B9"
                
                for d_item in row["All_Dates"]:
                    if d_item in date_range:
                        d_idx = np.where(date_range == d_item)[0][0]
                        if is_holiday(d_item):
                            self.ax.barh(y_idx, 1.0, left=d_idx - 0.5, color="none", edgecolor=bar_color, height=0.6, hatch='///////', alpha=1.0, zorder=3)

            try:
                for _, row in df.iterrows():
                    t_name = row["Task"]
                    raw_pre = row.get("Pre", "-")
                    if not raw_pre or raw_pre == "-":
                        continue
                    preds = [p.strip() for p in str(raw_pre).split(",") if p.strip()]
                    
                    if t_name not in task_list:
                        continue
                    y_B = num_tasks - 1 - task_list.index(t_name)
                    b_start_d = row["All_Dates"][0]
                    
                    b_start_idx = np.where(date_range == b_start_d)[0]
                    if len(b_start_idx) == 0:
                        continue
                    x_B_start = b_start_idx[0] - 0.5

                    for p_name in preds:
                        if p_name not in task_list:
                            continue
                        y_A = num_tasks - 1 - task_list.index(p_name)
                        a_row = next((item for item in processed_tasks if item["Task"] == p_name), None)
                        if not a_row:
                            continue
                        a_end_d = a_row["All_Dates"][-1]
                        
                        a_end_idx = np.where(date_range == a_end_d)[0]
                        if len(a_end_idx) == 0:
                            continue
                        x_A_end = a_end_idx[0] + 0.5

                        self.ax.plot(x_A_end, y_A, marker='o', markersize=4.5, color="#E74C3C", zorder=5)

                        connstyle = "arc3,rad=0" if y_A == y_B else "angle,angleA=0,angleB=90,rad=0"
                        
                        self.ax.annotate(
                            "",
                            xy=(x_B_start, y_B), xytext=(x_A_end, y_A),
                            xycoords='data', textcoords='data',
                            arrowprops=dict(arrowstyle="-|>", color="#E74C3C", lw=1.3, 
                                            connectionstyle=connstyle, patchA=None, patchB=None, shrinkA=0, shrinkB=2, zorder=4)
                        )
            except Exception as arrow_err:
                print(f"Σφάλμα κατά τη σχεδίαση βελών: {arrow_err}")

            y_day_num = num_tasks      
            y_day_let = num_tasks + 0.8  
            y_month = num_tasks + 1.7    

            days_gr = {0: "Δ", 1: "Τ", 2: "Τ", 3: "Π", 4: "Π", 5: "Σ", 6: "Κ"}
            
            for idx, d in enumerate(date_range):
                holiday_flag = is_holiday(d)
                color = "red" if holiday_flag else "black"
                
                self.ax.text(idx, y_day_num, str(d.day), ha='center', va='center', 
                        fontsize=8.5, fontweight='bold', color=color)
                
                self.ax.text(idx, y_day_let, days_gr[d.weekday()], ha='center', va='center', 
                        fontsize=8.5, fontweight='bold', color=color)

            months_gr = {
                1: "Ιαν", 2: "Φεβ", 3: "Μάρ", 4: "Απρ",
                5: "Μάι", 6: "Ιούν", 7: "Ιούλ", 8: "Αύγ",
                9: "Σεπ", 10: "Οκτ", 11: "Νοε", 12: "Δεκ"
            }
            
            month_spans = []
            current_month = None
            start_i = 0
            
            for idx, d in enumerate(date_range):
                m_key = (d.year, d.month)
                if current_month is None:
                    current_month = m_key
                    start_i = idx
                elif current_month != m_key:
                    month_spans.append((current_month, start_i, idx - 1))
                    current_month = m_key
                    start_i = idx
            if current_month is not None:
                month_spans.append((current_month, start_i, len(date_range) - 1))

            month_colors = ["#2C3E50", "#4A6B82"]

            for i, ((y, m), s_idx, e_idx) in enumerate(month_spans):
                width = e_idx - s_idx + 1
                bar_left = s_idx - 0.5
                
                m_color = month_colors[i % len(month_colors)]
                
                self.ax.barh(y_month, width, left=bar_left, height=0.7, 
                        color=m_color, edgecolor="#1A252F", alpha=0.9, zorder=3)
                
                m_name = months_gr[m]
                center_x = s_idx + (width - 1) / 2.0
                self.ax.text(center_x, y_month, f"{m_name} {y}", ha='center', va='center', 
                        color='white', fontweight='bold', fontsize=8.5, zorder=4)

            self.ax.set_yticks(range(num_tasks))
            self.ax.set_yticklabels([])

            for y_idx, t in enumerate(reversed(processed_tasks)):
                t_code = t["Task"]
                t_title = t["Title"] if t.get("Title", "").strip() else t_code
                wrapped_title = "\n".join(textwrap.wrap(t_title, width=15))

                self.ax.text(-0.9, y_idx, t_code, ha='center', va='center', 
                             fontsize=12, fontweight='bold', color='red')

                self.ax.text(-1.3, y_idx, wrapped_title, ha='right', va='center', 
                             fontsize=9, fontweight='bold', color='black')

            self.ax.set_xlim(-0.5, len(date_range) - 0.5)
            self.ax.set_ylim(-0.7, num_tasks + 2.5)
            self.ax.set_xticks(range(len(date_range)))
            self.ax.set_xticklabels([])

            for i in range(-1, len(date_range)):
                self.ax.axvline(x=i + 0.5, color='gray', linestyle='--', alpha=0.4, zorder=1)

            for y in range(num_tasks - 1):
                self.ax.axhline(y = y + 0.5, color='gray', linestyle='--', alpha=0.4, zorder=1)

            self.ax.axhline(y = num_tasks - 0.5, color='gray', linestyle='-', linewidth=0.8)
            self.ax.axhline(y = num_tasks + 0.4, color='gray', linestyle='-', linewidth=0.5)
            self.ax.axhline(y = num_tasks + 1.2, color='gray', linestyle='-', linewidth=0.5)

            self.ax.set_ylabel("")
            
            self.ax.set_title("Διάγραμμα Gantt", pad=12, fontsize=14, fontweight="bold", color="black", loc="center")
            
            proj_title_text = self.proj_title_entry.get().strip()
            if proj_title_text:
                self.ax.text(0.5, 1.08, proj_title_text, transform=self.ax.transAxes, 
                             ha='center', va='bottom', fontsize=18, fontweight="bold", color="#800080")
            
            self.fig.subplots_adjust(left=0.13, right=0.98, top=0.83, bottom=0.12)

        canvas = FigureCanvasTkAgg(self.fig, master=self.plot_frame)
        canvas.draw()
        
        canvas.mpl_connect("button_press_event", self.on_press)
        canvas.mpl_connect("button_press_event", self.on_plot_click)
        canvas.mpl_connect("motion_notify_event", self.on_motion)
        canvas.mpl_connect("button_release_event", self.on_release)
        
        canvas_widget = canvas.get_tk_widget()
        canvas_widget.pack(fill=tk.BOTH, expand=True)
        
        self.plot_frame.update_idletasks()
        self.plot_canvas.configure(scrollregion=self.plot_canvas.bbox("all"))

if __name__ == "__main__":
    root = tk.Tk()
    app = GanttApp(root)
    root.mainloop()