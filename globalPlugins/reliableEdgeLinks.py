# -*- coding: UTF-8 -*-
"""A fast links list for Edge and Chrome, retaining exact NVDA link identities."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional
import threading
import time
import weakref

import wx
from wx.lib.scrolledpanel import ScrolledPanel
import addonHandler
import api
import browseMode
import config
import controlTypes
import inputCore
import globalPluginHandler
import gui
import ui
from logHandler import log
from scriptHandler import script

addonHandler.initTranslation()

ADDON_NAME = _("Linkliste für Edge und Chrome")
BROWSER_NAMES = {"msedge": "Microsoft Edge", "chrome": "Google Chrome"}
# Keep the existing identity and settings so installing 2.0 upgrades 1.x.
CONFIG_SECTION = "reliableEdgeLinks"

try:
    config.conf.spec[CONFIG_SECTION] = {
        "windowX": "integer(default=-1)",
        "windowY": "integer(default=-1)",
        "windowWidth": "integer(default=-1)",
        "windowHeight": "integer(default=-1)",
        "windowDpi": "integer(default=96)",
        "searchText": "string(default='')",
        "rememberSearch": "boolean(default=True)",
    }
except Exception:
    log.debugWarning("Reliable links: could not register configuration", exc_info=True)


def _safeText(value: Any) -> str:
    try:
        return " ".join(str(value).split()) if value is not None else ""
    except Exception:
        return ""


def _safeAttr(obj: Any, name: str, default: Any = None) -> Any:
    try:
        return getattr(obj, name, default)
    except Exception:
        return default


def _normalise(value: Any) -> str:
    return _safeText(value).casefold()


def _configSection():
    try:
        return config.conf[CONFIG_SECTION]
    except Exception:
        return None


@dataclass(frozen=True)
class LinkSignature:
    label: str


@dataclass(eq=False)
class LinkEntry:
    item: Any
    signature: LinkSignature
    displayText: str
    document: Any
    bufferHandle: Any
    documentUrl: Any


def _documentUsable(document: Any) -> bool:
    return bool(
        document is not None
        and _safeAttr(document, "isReady", False)
        and _safeAttr(document, "isAlive", False)
    )


def _bufferToken(document):
    handle = _safeAttr(document, "VBufHandle")
    # ctypes handles are mutable; retain the value, not the pointer wrapper.
    return _safeAttr(handle, "value", handle)


def _entryIsCurrent(document: Any, entry: LinkEntry) -> bool:
    """Never reinterpret a saved text offset after a document was replaced."""
    return bool(
        _documentUsable(document)
        and entry.document is document
        and _safeAttr(entry.item, "document", document) is document
        and entry.bufferHandle == _bufferToken(document)
        and entry.documentUrl == _safeAttr(document, "documentURL")
    )


def _clampRect(x, y, width, height, area):
    # Negative coordinates are valid on monitors left of/above the primary one.
    width = max(1, min(int(width), area.width))
    height = max(1, min(int(height), area.height))
    x = min(max(int(x), area.x), area.x + area.width - width)
    y = min(max(int(y), area.y), area.y + area.height - height)
    return wx.Rect(x, y, width, height)


class ReliableLinksDialog(wx.Dialog):
    def __init__(self, parent, plugin, document, entries, browserName, workArea):
        super().__init__(
            parent,
            title=_("Linkliste – {browser}").format(browser=browserName),
            style=wx.DEFAULT_DIALOG_STYLE | wx.RESIZE_BORDER,
        )
        self._pluginRef = weakref.ref(plugin)
        self._document = document
        self._allEntries = entries
        self._workArea = workArea
        self._searchText = ""
        self._searchCallLater = None
        self._intendedEntry: Optional[LinkEntry] = None
        self._activationPending = False
        self._closing = False
        self._populating = False
        self._treeItems = []
        self._resultAction = None
        self._buttonCols = 0
        self._lastLayoutWidth = None
        self._statusLabel = ""
        self._buildGui()
        self._bindEvents()
        query = self._getRememberedSearchText()
        if query and not any(_normalise(query) in _normalise(e.signature.label) for e in entries):
            query = ""
        self.searchCtrl.ChangeValue(query)
        self._populateTree(query)
        self._restoreGeometry()
        self._focusControl(self.linksTree)

    def _buildGui(self):
        # Native controls, system colours and system fonts retain high-contrast
        # support and screen-reader semantics. No fixed pixel font or row height.
        self.panel = panel = ScrolledPanel(self, style=wx.TAB_TRAVERSAL)
        panel.SetName(_("Linkliste"))
        self.outer = outer = wx.BoxSizer(wx.VERTICAL)
        border = self.FromDIP(16)
        gap = self.FromDIP(8)

        searchLabel = wx.StaticText(panel, label=_("&Suchen:"))
        font = searchLabel.GetFont()
        font.SetWeight(wx.FONTWEIGHT_BOLD)
        searchLabel.SetFont(font)
        self.searchCtrl = wx.TextCtrl(panel, style=wx.TE_PROCESS_ENTER)
        self.searchCtrl.SetName(_("Suchen"))
        self.searchCtrl.SetHint(_("Linktext eingeben"))
        self.searchCtrl.SetMinSize(wx.Size(1, max(self.searchCtrl.GetBestSize().height, self.FromDIP(30))))
        outer.Add(searchLabel, 0, wx.LEFT | wx.RIGHT | wx.TOP, border)
        fieldSizer = wx.BoxSizer(wx.VERTICAL)
        fieldSizer.Add(self.searchCtrl, 0, wx.EXPAND | wx.TOP, self.FromDIP(5))
        outer.Add(fieldSizer, 0, wx.EXPAND | wx.LEFT | wx.RIGHT, border)
        outer.AddSpacer(self.FromDIP(14))

        listLabel = wx.StaticText(panel, label=_("&Links:"))
        listLabel.SetFont(font)
        self.linksTree = wx.TreeCtrl(panel, style=(
            wx.TR_HIDE_ROOT | wx.TR_SINGLE | wx.TR_NO_LINES
            | wx.TR_FULL_ROW_HIGHLIGHT | wx.BORDER_SIMPLE
        ))
        self.linksTree.SetName(_("Links"))
        self.linksTree.SetMinSize(self.FromDIP(wx.Size(1, 72)))
        self.treeRoot = self.linksTree.AddRoot("root")
        outer.Add(listLabel, 0, wx.LEFT | wx.RIGHT, border)
        outer.AddSpacer(self.FromDIP(5))
        outer.Add(self.linksTree, 1, wx.EXPAND | wx.LEFT | wx.RIGHT, border)
        outer.AddSpacer(gap)

        self.statusText = wx.StaticText(panel, label="", style=wx.ST_NO_AUTORESIZE)
        self.statusText.SetMinSize(wx.Size(1, max(self.statusText.GetCharHeight() + self.FromDIP(6), self.FromDIP(24))))
        outer.Add(self.statusText, 0, wx.EXPAND | wx.LEFT | wx.RIGHT, border)
        outer.AddSpacer(gap)
        outer.Add(wx.StaticLine(panel), 0, wx.EXPAND | wx.LEFT | wx.RIGHT, border)
        outer.AddSpacer(self.FromDIP(12))

        self.openButton = wx.Button(panel, wx.ID_OK, label=_("Link &öffnen"))
        self.jumpButton = wx.Button(panel, label=_("Zum Link s&pringen"))
        self.refreshButton = wx.Button(panel, label=_("Liste &aktualisieren"))
        self.closeButton = wx.Button(panel, wx.ID_CANCEL, label=_("S&chließen"))
        self._buttons = (self.openButton, self.jumpButton, self.refreshButton, self.closeButton)
        self._baseButtonLabels = tuple(b.GetLabel() for b in self._buttons)
        self.buttonSizer = wx.GridSizer(cols=4, hgap=gap, vgap=gap)
        self._measureButtons()
        for button in self._buttons:
            self.buttonSizer.Add(button, 0, wx.EXPAND)
        outer.Add(self.buttonSizer, 0, wx.EXPAND | wx.LEFT | wx.RIGHT, border)
        outer.AddSpacer(border)
        panel.SetSizer(outer)
        panel.SetupScrolling(scroll_x=True, scroll_y=True, scrollToTop=False)
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(panel, 1, wx.EXPAND)
        self.SetSizer(sizer)
        self.SetAffirmativeId(self.openButton.GetId())
        self.SetEscapeId(self.closeButton.GetId())
        self.openButton.SetDefault()

    def _measureButtons(self, available=None):
        for button, baseLabel in zip(self._buttons, self._baseButtonLabels):
            label = baseLabel
            if available is not None:
                # Native buttons support multiline captions. At extreme text
                # sizes wrap at word boundaries before requiring scrolling.
                lines, line = [], ""
                for word in baseLabel.split():
                    candidate = (line + " " + word).strip()
                    if line and button.GetTextExtent(candidate.replace("&", "")).width > max(1, available - self.FromDIP(28)):
                        lines.append(line)
                        line = word
                    else:
                        line = candidate
                label = "\n".join(lines + [line])
            button.SetLabel(label)
            button.SetMinSize(wx.DefaultSize)
            button.InvalidateBestSize()
        self._buttonWidth = max(b.GetBestSize().width for b in self._buttons) + self.FromDIP(12)
        height = max(self.FromDIP(34), max(b.GetBestSize().height for b in self._buttons))
        for button in self._buttons:
            button.SetMinSize(wx.Size(self._buttonWidth, height))

    def _bindEvents(self):
        self.searchCtrl.Bind(wx.EVT_TEXT, self._onSearch)
        self.searchCtrl.Bind(wx.EVT_TEXT_ENTER, self._onOpen)
        self.linksTree.Bind(wx.EVT_TREE_ITEM_ACTIVATED, self._onOpen)
        self.linksTree.Bind(wx.EVT_TREE_SEL_CHANGED, self._onTreeSelectionChanged)
        self.linksTree.Bind(wx.EVT_SET_FOCUS, self._onTreeSetFocus)
        self.openButton.Bind(wx.EVT_BUTTON, self._onOpen)
        self.jumpButton.Bind(wx.EVT_BUTTON, self._onJump)
        self.refreshButton.Bind(wx.EVT_BUTTON, self._onRefresh)
        self.closeButton.Bind(wx.EVT_BUTTON, self._onCancel)
        self.Bind(wx.EVT_CHAR_HOOK, self._onCharHook)
        self.Bind(wx.EVT_CLOSE, self._onCancel)
        self.Bind(wx.EVT_SIZE, self._onSize)
        self.Bind(wx.EVT_WINDOW_DESTROY, self._onDestroy)
        for control in (self.searchCtrl,) + self._buttons:
            control.Bind(wx.EVT_SET_FOCUS, self._onControlFocus)
        if hasattr(wx, "EVT_DPI_CHANGED"):
            self.Bind(wx.EVT_DPI_CHANGED, self._onDpiChanged)

    def _focusControl(self, control):
        control.SetFocus()
        self.panel.ScrollChildIntoView(control)

    def _onControlFocus(self, evt):
        self.panel.ScrollChildIntoView(evt.GetEventObject())
        evt.Skip()

    def _tab(self, backwards=False):
        self._clearSearchText()
        controls = [c for c in (self.searchCtrl, self.linksTree) + self._buttons if c.IsEnabled()]
        try:
            index = controls.index(wx.Window.FindFocus())
        except ValueError:
            index = 0
        self._focusControl(controls[(index + (-1 if backwards else 1)) % len(controls)])

    def _getRememberedSearchText(self):
        section = _configSection()
        if section is not None and section.get("rememberSearch", True):
            return _safeText(section.get("searchText", ""))
        return ""

    def _restoreGeometry(self):
        area = self._workArea
        maxW, maxH = max(1, int(area.width * .96)), max(1, int(area.height * .94))
        minW = min(max(self.FromDIP(300), self._buttonWidth + self.FromDIP(32)), maxW)
        minH = min(self.FromDIP(340), maxH)
        self.SetMinSize(wx.Size(minW, minH))
        w, h = min(self.FromDIP(840), maxW), min(self.FromDIP(540), maxH)
        x, y = area.x + (area.width - w) // 2, area.y + (area.height - h) // 2
        section = _configSection()
        if section is not None:
            try:
                oldW, oldH = int(section.get("windowWidth", -1)), int(section.get("windowHeight", -1))
                if oldW > 0 and oldH > 0:
                    # Positions are physical monitor coordinates; sizes follow DPI.
                    ratio = self.GetDPI().width / max(1, int(section.get("windowDpi", 96)))
                    w = min(max(round(oldW * ratio), minW), maxW)
                    h = min(max(round(oldH * ratio), minH), maxH)
                    x, y = int(section.get("windowX", x)), int(section.get("windowY", y))
            except Exception:
                log.debugWarning("Reliable links: invalid saved window state", exc_info=True)
        self.SetSize(_clampRect(x, y, w, h, area))
        self._layoutButtons()

    def _layoutButtons(self):
        available = max(1, self.GetClientSize().width - self.FromDIP(32))
        if available != self._lastLayoutWidth:
            self._lastLayoutWidth = available
            self._measureButtons(available)
        gap = self.FromDIP(8)
        cols = next((c for c in (4, 2, 1) if c * self._buttonWidth + (c - 1) * gap <= available), 1)
        if cols != self._buttonCols:
            self._buttonCols = cols
            self.buttonSizer.SetCols(cols)
        self.statusText.SetLabel(self._statusLabel)
        self.statusText.Wrap(available)
        self.statusText.SetMinSize(wx.Size(1, max(self.statusText.GetBestSize().height, self.FromDIP(24))))
        self.Layout()
        self.panel.Layout()
        # On very short work areas the complete form remains reachable by
        # scrolling and Tab; on ordinary screens only the links tree scrolls.
        self.panel.FitInside()

    def _onSize(self, evt):
        if not self._closing:
            self._layoutButtons()
        evt.Skip()

    def _onDpiChanged(self, evt):
        evt.Skip()
        wx.CallAfter(self._afterDpiChange)

    def _afterDpiChange(self):
        if self._closing or not self:
            return
        self._measureButtons()
        self._lastLayoutWidth = None
        self._layoutButtons()
        index = wx.Display.GetFromWindow(self)
        if index != wx.NOT_FOUND:
            area = wx.Display(index).GetClientArea()
            self.SetSize(_clampRect(*self.GetRect(), area))

    def _saveDialogState(self):
        section = _configSection()
        if section is None:
            return
        try:
            if not self.IsIconized() and not self.IsMaximized():
                rect = self.GetRect()
                for key, value in zip(("windowX", "windowY", "windowWidth", "windowHeight"), rect):
                    section[key] = int(value)
                section["windowDpi"] = self.GetDPI().width
            section["searchText"] = self.searchCtrl.GetValue() if section.get("rememberSearch", True) else ""
        except Exception:
            log.debugWarning("Reliable links: could not save window state", exc_info=True)

    def _finish(self, result, action=None):
        if self._closing:
            return
        self._saveDialogState()
        self._clearSearchText()
        self._resultAction = action
        self._closing = True
        self.EndModal(result)

    def _onCancel(self, evt):
        self._finish(wx.ID_CANCEL)

    def _onDestroy(self, evt):
        if evt.GetEventObject() is self:
            self._closing = True
            self._clearSearchText()
        evt.Skip()

    def _onSearch(self, evt):
        self._clearSearchText()
        self._populateTree(self.searchCtrl.GetValue())
        evt.Skip()

    def _populateTree(self, query=""):
        previous = self._getSelectedEntry()
        self._populating = True
        self.linksTree.Freeze()
        try:
            self._intendedEntry = None
            self._treeItems = []
            self.linksTree.DeleteChildren(self.treeRoot)
            query = _normalise(query)
            chosen = None
            for entry in self._allEntries:
                if query and query not in _normalise(entry.signature.label):
                    continue
                item = self.linksTree.AppendItem(self.treeRoot, entry.displayText)
                self.linksTree.SetItemData(item, entry)
                self._treeItems.append(item)
                if previous is entry:
                    chosen = item
            if self._treeItems:
                self._selectTreeItem(chosen or self._treeItems[0])
        finally:
            self._populating = False
            self.linksTree.Thaw()
        count, total = len(self._treeItems), len(self._allEntries)
        if not count:
            status = _("Keine Treffer – Suche ändern oder leeren.") if total else _("Keine Links gefunden. Liste bei Bedarf aktualisieren.")
        elif query:
            status = _("{visible} von {total} Links").format(visible=count, total=total)
        else:
            status = _("1 Link insgesamt") if total == 1 else _("{count} Links insgesamt").format(count=total)
        self._statusLabel = status
        self.statusText.SetLabel(status)
        self.openButton.Enable(bool(count))
        self.jumpButton.Enable(bool(count))
        self._layoutButtons()

    def _getSelectedEntry(self):
        # Type-ahead and arrow commands update this synchronously. Enter must
        # not overtake a native tree selection notification.
        if self._intendedEntry is not None:
            return self._intendedEntry
        item = self.linksTree.GetSelection()
        if item and item.IsOk():
            entry = self.linksTree.GetItemData(item)
            if entry is not None:
                return entry
        return self._intendedEntry

    def _selectTreeItem(self, item):
        if not item or not item.IsOk():
            self._intendedEntry = None
            return
        self._intendedEntry = self.linksTree.GetItemData(item)
        self.linksTree.SelectItem(item)
        self.linksTree.EnsureVisible(item)

    def _onTreeSelectionChanged(self, evt):
        item = evt.GetItem()
        if not self._populating and item and item.IsOk() and item == self.linksTree.GetSelection():
            self._intendedEntry = self.linksTree.GetItemData(item)
        evt.Skip()

    def _chooseAction(self, kind):
        if self._closing or self._activationPending:
            return
        entry = self._getSelectedEntry()
        if entry is None:
            ui.message(_("Kein Link ausgewählt."))
            return
        if self._pluginRef() is None or not _entryIsCurrent(self._document, entry):
            ui.message(_("Die Webseite hat sich geändert. Bitte aktualisieren Sie die Linkliste."))
            return
        self._activationPending = True
        self._finish(wx.ID_OK, (kind, entry))

    def _onOpen(self, evt):
        self._chooseAction("open")

    def _onJump(self, evt):
        self._chooseAction("jump")

    def _onRefresh(self, evt):
        plugin = self._pluginRef()
        if plugin is None or not _documentUsable(self._document):
            ui.message(_("Die Webseite ist nicht mehr verfügbar. Bitte schließen Sie die Linkliste und öffnen Sie sie auf der gewünschten Seite erneut."))
            return
        try:
            entries = plugin.collectLinks(self._document)
        except Exception:
            log.exception("Reliable links: refresh failed")
            ui.message(_("Die Liste konnte nicht aktualisiert werden. Die bisherige Liste bleibt erhalten."))
            return
        self._allEntries = entries
        self._clearSearchText()
        self.searchCtrl.ChangeValue("")
        self._populateTree()
        self.linksTree.SetFocus()
        ui.message(_("Linkliste aktualisiert. {count} Links.").format(count=len(entries)))

    def replayCapturedInput(self, commands):
        for command, value in commands:
            if self._closing or not self.IsShown():
                break
            if command == "character":
                self._handleTypeAheadCharacter(value)
            elif command == "enter":
                self._chooseAction("open")
            elif command == "escape":
                self._finish(wx.ID_CANCEL)
            elif command == "navigate":
                self._navigate(value)
            elif command == "backspace":
                self._clearSearchText()

    def _onTreeSetFocus(self, evt):
        self._clearSearchText()
        self.panel.ScrollChildIntoView(self.linksTree)
        evt.Skip()

    def _clearSearchText(self):
        if self._searchCallLater is not None:
            self._searchCallLater.Stop()
            self._searchCallLater = None
        self._searchText = ""

    def _search(self, searchText):
        if not self._treeItems:
            return False
        current = self.linksTree.GetSelection()
        try:
            start = self._treeItems.index(current)
        except ValueError:
            start = 0
        if len(searchText) == 1:
            start = (start + 1) % len(self._treeItems)
        for offset in range(len(self._treeItems)):
            item = self._treeItems[(start + offset) % len(self._treeItems)]
            if self.linksTree.GetItemText(item).casefold().startswith(searchText):
                self._selectTreeItem(item)
                return True
        wx.Bell()
        return False

    def _handleTypeAheadCharacter(self, char):
        char = char.casefold()
        if self._searchText != char:
            self._searchText += char
        if self._searchCallLater is not None:
            self._searchCallLater.Stop()
        self._searchCallLater = wx.CallLater(1000, self._clearSearchText)
        self._search(self._searchText)

    def _navigate(self, key):
        self._clearSearchText()
        if not self._treeItems:
            return
        try:
            index = self._treeItems.index(self.linksTree.GetSelection())
        except ValueError:
            index = 0
        page = max(1, self.linksTree.GetClientSize().height // max(1, self.linksTree.GetCharHeight()) - 1)
        if key == "home":
            index = 0
        elif key == "end":
            index = len(self._treeItems) - 1
        else:
            index += {"up": -1, "down": 1, "pageup": -page, "pagedown": page}.get(key, 0)
        self._selectTreeItem(self._treeItems[min(max(index, 0), len(self._treeItems) - 1)])

    def _onCharHook(self, evt):
        key = evt.GetKeyCode()
        if key == wx.WXK_ESCAPE:
            self._finish(wx.ID_CANCEL)
            return
        if key == wx.WXK_TAB and not evt.ControlDown() and not evt.AltDown():
            self._tab(evt.ShiftDown())
            return
        if evt.AltDown() and not evt.ControlDown() and key in (ord("1"), ord("2"), ord("3")):
            if key == ord("1"):
                self._focusControl(self.linksTree)
            elif key == ord("2"):
                self._focusControl(self.searchCtrl)
                self.searchCtrl.SelectAll()
            else:
                self._onRefresh(evt)
            return
        focus = wx.Window.FindFocus()
        if focus in (None, self, self.linksTree) and not evt.ControlDown() and not evt.AltDown():
            if key in (wx.WXK_RETURN, wx.WXK_NUMPAD_ENTER):
                self._chooseAction("open")
                return
            nav = {wx.WXK_UP: "up", wx.WXK_DOWN: "down", wx.WXK_HOME: "home", wx.WXK_END: "end",
                   wx.WXK_PAGEUP: "pageup", wx.WXK_PAGEDOWN: "pagedown"}
            if key in nav:
                self._navigate(nav[key])
                return
            if key == wx.WXK_BACK:
                self._clearSearchText()
                return
            unicodeKey = evt.GetUnicodeKey()
            if unicodeKey != wx.WXK_NONE and unicodeKey >= 32:
                self._handleTypeAheadCharacter(chr(unicodeKey))
                return
            if key == wx.WXK_TAB:
                self._clearSearchText()
        evt.Skip()


class GlobalPlugin(globalPluginHandler.GlobalPlugin):
    scriptCategory = ADDON_NAME

    def __init__(self):
        super().__init__()
        self._captureLock = threading.Lock()
        self._previousCaptureFunc = None
        self._earlyInputCommands = []
        self._capturingEarlyInput = False
        self._captureStarted = 0.0
        self._dialogPending = False
        self._dialog = None
        self._terminated = False

    def terminate(self):
        self._terminated = True
        self._stopEarlyInputCapture()
        if self._dialog is not None and not self._dialog._closing:
            self._dialog._finish(wx.ID_CANCEL)
        super().terminate()

    def _startEarlyInputCapture(self):
        with self._captureLock:
            if self._capturingEarlyInput or getattr(inputCore.manager, "_captureFunc", None) is not None:
                return
            self._earlyInputCommands = []
            self._captureStarted = time.monotonic()
            self._previousCaptureFunc = None
            self._capturingEarlyInput = True
            inputCore.manager._captureFunc = self._captureEarlyGesture

    def _stopEarlyInputCapture(self):
        with self._captureLock:
            if self._capturingEarlyInput and getattr(inputCore.manager, "_captureFunc", None) == self._captureEarlyGesture:
                inputCore.manager._captureFunc = self._previousCaptureFunc
            self._capturingEarlyInput = False
            commands, self._earlyInputCommands = self._earlyInputCommands, []
            self._previousCaptureFunc = None
            return commands

    def _captureEarlyGesture(self, gesture):
        # Never consume Alt/Ctrl/Windows combinations (e.g. Alt+Tab). NVDA may
        # still be releasing from the opening chord, so permit that modifier.
        key = _safeText(_safeAttr(gesture, "mainKeyName", "")).lower()
        modifiers = {str(m).lower() for m in _safeAttr(gesture, "modifierNames", ())}
        if modifiers - {"shift", "nvda"}:
            return True
        if key in {"enter", "numpadenter"}:
            command = ("enter", "")
        elif key == "escape":
            command = ("escape", "")
        elif key in {"uparrow", "downarrow", "up", "down", "home", "end", "pageup", "pagedown"}:
            command = ("navigate", {"uparrow": "up", "downarrow": "down"}.get(key, key))
        elif key == "backspace":
            command = ("backspace", "")
        else:
            char = _safeAttr(gesture, "character")
            if not isinstance(char, str) or not char or not char.isprintable():
                char = key if len(key) == 1 and key.isprintable() else ""
            if not char:
                return True
            command = ("character", char)
        with self._captureLock:
            if not self._capturingEarlyInput or time.monotonic() - self._captureStarted > 5:
                return True
            # Atomic handoff: a key is either consumed here or handled by wx.
            self._earlyInputCommands.append(command)
        return False

    def _handoffCapturedInput(self, dialog):
        commands = self._stopEarlyInputCapture()
        if dialog and not dialog._closing and dialog.IsShown():
            dialog.replayCapturedInput(commands)

    @script(description=_("Öffnet die zuverlässige Linkliste in Microsoft Edge oder Google Chrome"),
            category=ADDON_NAME, gesture="kb:NVDA+f8")
    def script_showReliableLinks(self, gesture):
        if self._terminated:
            return
        if self._dialog is not None:
            self._dialog.Raise()
            self._dialog.linksTree.SetFocus()
            return
        if self._dialogPending:
            return
        focus = api.getFocusObject()
        appName = _normalise(_safeAttr(_safeAttr(focus, "appModule"), "appName"))
        if appName not in BROWSER_NAMES:
            ui.message(_("Diese Linkliste ist in Microsoft Edge und Google Chrome verfügbar."))
            return
        document = _safeAttr(focus, "treeInterceptor")
        if not _documentUsable(document):
            ui.message(_("Für die aktuelle Seite ist noch kein NVDA-Browsemodus verfügbar. Warten Sie, bis die Seite geladen ist, und versuchen Sie es erneut."))
            return
        if not callable(_safeAttr(document, "_iterNodesByType")):
            ui.message(_("Die aktuelle Seite unterstützt keine Linkliste."))
            return
        self._dialogPending = True
        self._startEarlyInputCapture()
        try:
            entries = self.collectLinks(document)
        except Exception:
            self._dialogPending = False
            self._stopEarlyInputCapture()
            log.exception("Reliable links: collecting links failed")
            ui.message(_("Die Links konnten nicht ermittelt werden. Bitte versuchen Sie es erneut, sobald die Seite vollständig geladen ist."))
            return
        root = _safeAttr(document, "rootNVDAObject")
        location = _safeAttr(root, "location")
        try:
            point = wx.Point(int(location.left + location.width / 2), int(location.top + location.height / 2))
            displayIndex = wx.Display.GetFromPoint(point)
        except Exception:
            displayIndex = wx.NOT_FOUND
        if displayIndex == wx.NOT_FOUND:
            displayIndex = wx.Display.GetFromWindow(gui.mainFrame)
        area = wx.Display(0 if displayIndex == wx.NOT_FOUND else displayIndex).GetClientArea()

        def runDialog():
            dialog = None
            prepared = False
            action = None
            try:
                if self._terminated:
                    return
                gui.mainFrame.prePopup()
                prepared = True
                dialog = ReliableLinksDialog(gui.mainFrame, self, document, entries, BROWSER_NAMES[appName], area)
                self._dialog = dialog
                wx.CallAfter(self._handoffCapturedInput, dialog)
                dialog.ShowModal()
                action = dialog._resultAction
            except Exception:
                log.exception("Reliable links: dialog failed")
                ui.message(_("Die Linkliste konnte nicht geöffnet werden."))
            finally:
                self._stopEarlyInputCapture()
                self._dialog = None
                self._dialogPending = False
                if dialog is not None:
                    dialog.Destroy()
                if prepared:
                    gui.mainFrame.postPopup()
            # Restore the browser before invoking the exact link, so popup
            # teardown cannot steal focus from a new page or a site dialog.
            if action and not self._terminated:
                kind, entry = action
                if kind == "open":
                    self.activateEntry(document, entry)
                else:
                    self.moveToEntry(document, entry)
        wx.CallAfter(runDialog)

    script_showReliableLinks.ignoreTreeInterceptorPassThrough = True

    def collectLinks(self, document):
        """Enumerate the entire NVDA document; never cap or deduplicate links.

        Keep exact QuickNav items, including image/unnamed/duplicate links and
        frames. Do not walk the live cross-process tree during list construction.
        IA2 and UIA backends expose their own iterator through the same API.
        """
        if not _documentUsable(document):
            raise RuntimeError("Document unavailable")
        bufferHandle = _bufferToken(document)
        url = _safeAttr(document, "documentURL")
        entries = []
        for item in document._iterNodesByType("link", direction="next", pos=None):
            label = _safeText(_safeAttr(item, "label"))
            if not label:
                label = _safeText(_safeAttr(_safeAttr(item, "textInfo"), "text")) or _("Unbenannter Link")
            entries.append(LinkEntry(item, LinkSignature(label), label, document, bufferHandle, url))
        if not _documentUsable(document) or bufferHandle != _bufferToken(document) or url != _safeAttr(document, "documentURL"):
            raise RuntimeError("Document changed during collection")
        return entries

    def _resolveExactLinkObject(self, document, selected):
        if not _entryIsCurrent(document, selected):
            return None
        try:
            obj = selected.item.obj
            # Some backends return a descendant; follow only its own ancestry.
            # No name matching, index, neighbouring element or mouse fallback.
            seen = set()
            for _ in range(32):
                if obj is None or id(obj) in seen or bool(getattr(obj, "isDefunct", False)):
                    return None
                seen.add(id(obj))
                states = getattr(obj, "states", set())
                if controlTypes.State.DEFUNCT in states or controlTypes.State.UNAVAILABLE in states:
                    return None
                if obj.role == controlTypes.Role.LINK:
                    identifier = _safeAttr(selected.item, "vbufFieldIdentifier")
                    getIdentifier = _safeAttr(document, "getIdentifierFromNVDAObject")
                    if identifier is not None and callable(getIdentifier) and tuple(getIdentifier(obj)) != tuple(identifier):
                        return None
                    return obj
                if obj.role == controlTypes.Role.DOCUMENT:
                    return None
                obj = obj.parent
        except Exception:
            log.debugWarning("Reliable links: exact link unavailable", exc_info=True)
        return None

    def activateEntry(self, document, selected):
        obj = self._resolveExactLinkObject(document, selected)
        if obj is None:
            ui.message(_("Der ausgewählte Link ist nicht mehr eindeutig verfügbar. Es wurde nichts aktiviert. Bitte öffnen Sie die Linkliste erneut."))
            return
        try:
            action = getattr(obj, "doAction", None)
            if not callable(action):
                raise NotImplementedError
            action()
        except Exception:
            log.exception("Reliable links: direct link activation failed")
            ui.message(_("Der ausgewählte Link konnte nicht aktiviert werden. Es wurde kein anderer Link geöffnet."))

    def moveToEntry(self, document, selected):
        obj = self._resolveExactLinkObject(document, selected)
        if obj is None:
            ui.message(_("Der ausgewählte Link ist nicht mehr verfügbar. Bitte öffnen Sie die Linkliste erneut."))
            return
        try:
            # Resolve a fresh position from this exact object. A live page may
            # insert text while the list is open, invalidating old text offsets.
            info = document.makeTextInfo(obj)
            browseMode.TextInfoQuickNavItem("link", document, info).moveTo()
            ui.message(_("Zum Link gesprungen: {label}").format(label=selected.signature.label))
        except Exception:
            log.exception("Reliable links: move to link failed")
            ui.message(_("Der ausgewählte Link konnte nicht angesprungen werden."))
