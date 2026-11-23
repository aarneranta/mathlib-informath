"""Whether a reading is fully worded: no constant of its declaration is left
as \\mathrm{c}, which Informath writes when the symbol table has no form for
it that fits. A multi-letter variable (hx, motive, self) is also written
upright, as \\mathrm{hx}, but is not a constant; the two are told apart by the
declaration's Dedukti: c is a constant if it occurs free there, a variable
if it is bound or not there at all (a name made by NLG).

Used by coverage.py and build-html.py."""
import re

UPRIGHT = re.compile(r'\\mathrm\{([^{}]*)\}')
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
BINDER = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:|([A-Za-z_][A-Za-z0-9_']*)\s*=>")


def free_identifiers(dedukti):
    """The identifiers of a Dedukti declaration that no binder of it binds
    (its own name among them; Dedukti has no shadowing that matters here)."""
    text = re.sub(r'\(;.*?;\)', ' ', dedukti or '', flags=re.S)
    bound = {a or b for a, b in BINDER.findall(text)}
    # the declared name is free, though "c :" looks like a binder
    head = re.match(r"\s*(?:def\s+|thm\s+|inj\s+)?([A-Za-z_][A-Za-z0-9_']*)", text)
    if head:
        bound.discard(head.group(1))
    return set(IDENT.findall(text)) - bound


def symbolic_constants(text, dedukti):
    """The constants of the declaration that a reading shows as \\mathrm{c}."""
    free = free_identifiers(dedukti)
    out = []
    for m in UPRIGHT.findall(text or ''):
        name = m.replace('\\_', '_').replace("\\'", "'")
        if name in free:
            out.append(name)
    return out


def worded(text, dedukti):
    """A reading that exists and shows no constant as \\mathrm{c}."""
    return bool(text) and not symbolic_constants(text, dedukti)
