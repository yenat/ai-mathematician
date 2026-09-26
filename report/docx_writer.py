"""Minimal .docx writer, standard library only (this machine has no pip).

A .docx is a zip of WordprocessingML parts. This writes the few parts Word
needs, with built-in heading styles, so the result opens in Word,
LibreOffice and Google Docs and gets a navigable outline.

    doc = Doc()
    doc.heading("Title", 0)
    doc.para("Plain text with **bold** and `code`.")
    doc.bullets(["one", "two"])
    doc.table([["h1", "h2"], ["a", "b"]])
    doc.save("out.docx")
"""
import re
import zipfile
from xml.sax.saxutils import escape

_NS = ('xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" '
       'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"')

_STYLES = f"""<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:styles {_NS}>
<w:docDefaults><w:rPrDefault><w:rPr>
<w:rFonts w:ascii="Calibri" w:hAnsi="Calibri" w:cs="Calibri"/><w:sz w:val="22"/>
</w:rPr></w:rPrDefault><w:pPrDefault><w:pPr><w:spacing w:after="120" w:line="276" w:lineRule="auto"/></w:pPr></w:pPrDefault></w:docDefaults>
<w:style w:type="paragraph" w:default="1" w:styleId="Normal"><w:name w:val="Normal"/></w:style>
<w:style w:type="paragraph" w:styleId="Title"><w:name w:val="Title"/><w:basedOn w:val="Normal"/>
<w:pPr><w:spacing w:after="240"/></w:pPr><w:rPr><w:b/><w:color w:val="1F3864"/><w:sz w:val="40"/></w:rPr></w:style>
<w:style w:type="paragraph" w:styleId="Heading1"><w:name w:val="heading 1"/><w:basedOn w:val="Normal"/>
<w:pPr><w:keepNext/><w:spacing w:before="360" w:after="120"/><w:outlineLvl w:val="0"/></w:pPr>
<w:rPr><w:b/><w:color w:val="1F3864"/><w:sz w:val="30"/></w:rPr></w:style>
<w:style w:type="paragraph" w:styleId="Heading2"><w:name w:val="heading 2"/><w:basedOn w:val="Normal"/>
<w:pPr><w:keepNext/><w:spacing w:before="240" w:after="80"/><w:outlineLvl w:val="1"/></w:pPr>
<w:rPr><w:b/><w:color w:val="2E5395"/><w:sz w:val="25"/></w:rPr></w:style>
<w:style w:type="paragraph" w:styleId="Code"><w:name w:val="Code"/><w:basedOn w:val="Normal"/>
<w:pPr><w:shd w:val="clear" w:color="auto" w:fill="F2F2F2"/><w:spacing w:after="0" w:line="240" w:lineRule="auto"/></w:pPr>
<w:rPr><w:rFonts w:ascii="Consolas" w:hAnsi="Consolas"/><w:sz w:val="18"/></w:rPr></w:style>
<w:style w:type="paragraph" w:styleId="Caption"><w:name w:val="caption"/><w:basedOn w:val="Normal"/>
<w:rPr><w:i/><w:color w:val="595959"/><w:sz w:val="18"/></w:rPr></w:style>
<w:style w:type="table" w:styleId="Grid"><w:name w:val="Table Grid"/>
<w:tblPr><w:tblBorders>
<w:top w:val="single" w:sz="4" w:color="A6A6A6"/><w:left w:val="single" w:sz="4" w:color="A6A6A6"/>
<w:bottom w:val="single" w:sz="4" w:color="A6A6A6"/><w:right w:val="single" w:sz="4" w:color="A6A6A6"/>
<w:insideH w:val="single" w:sz="4" w:color="A6A6A6"/><w:insideV w:val="single" w:sz="4" w:color="A6A6A6"/>
</w:tblBorders><w:tblCellMar><w:left w:w="100" w:type="dxa"/><w:right w:w="100" w:type="dxa"/></w:tblCellMar></w:tblPr></w:style>
</w:styles>"""

_NUMBERING = f"""<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:numbering {_NS}>
<w:abstractNum w:abstractNumId="0"><w:lvl w:ilvl="0"><w:start w:val="1"/><w:numFmt w:val="bullet"/>
<w:lvlText w:val="•"/><w:lvlJc w:val="left"/><w:pPr><w:ind w:left="720" w:hanging="360"/></w:pPr></w:lvl></w:abstractNum>
<w:abstractNum w:abstractNumId="1"><w:lvl w:ilvl="0"><w:start w:val="1"/><w:numFmt w:val="decimal"/>
<w:lvlText w:val="%1."/><w:lvlJc w:val="left"/><w:pPr><w:ind w:left="720" w:hanging="360"/></w:pPr></w:lvl></w:abstractNum>
<w:num w:numId="1"><w:abstractNumId w:val="0"/></w:num>
{{nums}}
</w:numbering>"""

_CT = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
<Default Extension="xml" ContentType="application/xml"/>
<Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/>
<Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"/>
<Override PartName="/word/numbering.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.numbering+xml"/>
<Override PartName="/docProps/core.xml" ContentType="application/vnd.openxmlformats-package.core-properties+xml"/>
</Types>"""

_RELS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/>
<Relationship Id="rId2" Type="http://schemas.openxmlformats.org/package/2006/relationships/metadata/core-properties" Target="docProps/core.xml"/>
</Relationships>"""

_DOC_RELS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>
<Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/numbering" Target="numbering.xml"/>
</Relationships>"""


def _rpr(bold=False, italic=False, code=False):
    """Run properties in the element order the schema requires
    (rFonts, b, i, color, sz -- likewise shd before spacing in paragraph
    properties); Word reports files that get this order wrong as corrupt."""
    s = ""
    if code:
        s += '<w:rFonts w:ascii="Consolas" w:hAnsi="Consolas"/>'
    if bold:
        s += "<w:b/>"
    if italic:
        s += "<w:i/>"
    if code:
        s += '<w:sz w:val="19"/>'
    return f"<w:rPr>{s}</w:rPr>" if s else ""


def _runs(text, bold=False):
    """Inline markup: **bold**, *italic*, `code`."""
    out = []
    for tok in re.split(r"(\*\*[^*]+\*\*|`[^`]+`|\*[^*]+\*)", text):
        if not tok:
            continue
        b, i, c = bold, False, False
        if tok.startswith("**"):
            tok, b = tok[2:-2], True
        elif tok.startswith("`"):
            tok, c = tok[1:-1], True
        elif tok.startswith("*"):
            tok, i = tok[1:-1], True
        out.append(f'<w:r>{_rpr(b, i, c)}'
                   f'<w:t xml:space="preserve">{escape(tok)}</w:t></w:r>')
    return "".join(out)


class Doc:
    def __init__(self, title="Report", author=""):
        self.body, self.title, self.author = [], title, author
        self._numbered = 0

    def _p(self, inner, style=None, extra=""):
        ppr = (f'<w:pStyle w:val="{style}"/>' if style else "") + extra
        self.body.append(f'<w:p>{"<w:pPr>" + ppr + "</w:pPr>" if ppr else ""}{inner}</w:p>')

    def heading(self, text, level=1):
        self._p(_runs(text), {0: "Title", 1: "Heading1", 2: "Heading2"}[level])

    def para(self, text, style=None):
        self._p(_runs(text), style)

    def caption(self, text):
        self._p(_runs(text), "Caption")

    def bullets(self, items):
        for it in items:
            self._p(_runs(it), None, '<w:numPr><w:ilvl w:val="0"/><w:numId w:val="1"/></w:numPr>')

    def numbered(self, items):
        self._numbered += 1
        nid = 1 + self._numbered
        for it in items:
            self._p(_runs(it), None,
                    f'<w:numPr><w:ilvl w:val="0"/><w:numId w:val="{nid}"/></w:numPr>')

    def code(self, text):
        for ln in text.splitlines() or [""]:
            self._p(f'<w:r><w:t xml:space="preserve">{escape(ln)}</w:t></w:r>', "Code")
        self._p("")

    def table(self, rows, header=True, widths=None):
        """rows: list of lists of cell text (inline markup allowed)."""
        ncol = len(rows[0])
        widths = widths or [9000 // ncol] * ncol
        grid = "".join(f'<w:gridCol w:w="{w}"/>' for w in widths)
        trs = []
        for i, row in enumerate(rows):
            cells = []
            for j, c in enumerate(row):
                shade = '<w:shd w:val="clear" w:color="auto" w:fill="DCE3EF"/>' if header and i == 0 else ""
                runs = _runs(str(c), bold=header and i == 0)
                cells.append(f'<w:tc><w:tcPr><w:tcW w:w="{widths[j]}" w:type="dxa"/>{shade}</w:tcPr>'
                             f'<w:p><w:pPr><w:spacing w:after="0"/></w:pPr>{runs}</w:p></w:tc>')
            # cantSplit keeps each row on one page; tblHeader repeats the
            # header row after a page break (schema order: cantSplit first)
            trh = "<w:trPr><w:cantSplit/>" + (
                "<w:tblHeader/>" if header and i == 0 else "") + "</w:trPr>"
            trs.append(f"<w:tr>{trh}{''.join(cells)}</w:tr>")
        self.body.append(f'<w:tbl><w:tblPr><w:tblStyle w:val="Grid"/><w:tblW w:w="0" w:type="auto"/></w:tblPr>'
                         f'<w:tblGrid>{grid}</w:tblGrid>{"".join(trs)}</w:tbl>')
        self._p("")

    def page_break(self):
        self.body.append('<w:p><w:r><w:br w:type="page"/></w:r></w:p>')

    def save(self, path):
        sect = ('<w:sectPr><w:pgSz w:w="11906" w:h="16838"/>'
                '<w:pgMar w:top="1300" w:right="1300" w:bottom="1300" w:left="1300" '
                'w:header="708" w:footer="708" w:gutter="0"/></w:sectPr>')
        doc = (f'<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n'
               f'<w:document {_NS}><w:body>{"".join(self.body)}{sect}</w:body></w:document>')
        nums = "".join(f'<w:num w:numId="{1 + k}"><w:abstractNumId w:val="1"/>'
                       f'<w:lvlOverride w:ilvl="0"><w:startOverride w:val="1"/></w:lvlOverride></w:num>'
                       for k in range(1, self._numbered + 1))
        core = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                '<cp:coreProperties xmlns:cp="http://schemas.openxmlformats.org/package/2006/metadata/core-properties" '
                'xmlns:dc="http://purl.org/dc/elements/1.1/">'
                f'<dc:title>{escape(self.title)}</dc:title><dc:creator>{escape(self.author)}</dc:creator>'
                '</cp:coreProperties>')
        with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
            z.writestr("[Content_Types].xml", _CT)
            z.writestr("_rels/.rels", _RELS)
            z.writestr("word/_rels/document.xml.rels", _DOC_RELS)
            z.writestr("word/document.xml", doc)
            z.writestr("word/styles.xml", _STYLES)
            z.writestr("word/numbering.xml", _NUMBERING.replace("{nums}", nums))
            z.writestr("docProps/core.xml", core)
