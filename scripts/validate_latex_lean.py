#!/usr/bin/env python3
"""validate_latex_lean.py — Cross-validate LaTeX source against Lean formalization.

Parses lamportform.tex and the ConnesLean/ Lean files to detect:
  1. LaTeX statements with no Lean counterpart
  2. Lean declarations not tracked in the concordance
  3. Axioms (trusted, not machine-checked)
  4. Proof-step coverage gaps within structured proofs
  5. Statement-level consistency warnings

Outputs a Markdown review checklist to stdout (pipe to a file for persistence).

Usage:
    python3 scripts/validate_latex_lean.py                  # full report to stdout
    python3 scripts/validate_latex_lean.py -o review.md     # write to file
    python3 scripts/validate_latex_lean.py --checklist-only  # only the TODO checklist
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class LatexStatement:
    """A formal statement extracted from the LaTeX source."""
    kind: str          # theorem, lemma, proposition, corollary, definition, remark
    label: str         # \label{...} if present, else ""
    title: str         # [Title] if present
    line: int          # 1-based line number of \begin{...}
    end_line: int = 0  # line of matching \end{...}
    section: str = ""  # enclosing \section title

@dataclass
class LatexProofStep:
    """A structured proof step from the LaTeX source."""
    level: str         # "Step", "Substep", "Subsubstep"
    number: str        # e.g. "1", "1.2", "1.2.3"
    text: str          # claim text (first ~120 chars)
    line: int
    parent_statement: str = ""  # label of enclosing theorem/lemma

@dataclass
class LeanDecl:
    """A declaration extracted from a Lean source file."""
    kind: str          # theorem, def, lemma, axiom, structure, abbrev, instance
    name: str          # fully qualified short name
    file: str          # relative path from repo root
    line: int          # 1-based line number
    has_sorry: bool = False
    has_proof: bool = True  # false for axiom

@dataclass
class ConcordanceEntry:
    """An entry from concordance.md mapping paper → Lean."""
    paper_result: str
    paper_lines: str
    lean_file: str
    lean_name: str
    status: str        # proved, axiom, not yet

@dataclass
class ValidationReport:
    """Aggregated validation results."""
    latex_statements: list[LatexStatement] = field(default_factory=list)
    latex_steps: list[LatexProofStep] = field(default_factory=list)
    lean_decls: list[LeanDecl] = field(default_factory=list)
    concordance: list[ConcordanceEntry] = field(default_factory=list)
    # Derived
    unformalized: list[LatexStatement] = field(default_factory=list)
    axioms: list[LeanDecl] = field(default_factory=list)
    untracked_lean: list[LeanDecl] = field(default_factory=list)
    sorry_decls: list[LeanDecl] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

# ---------------------------------------------------------------------------
# Parsers
# ---------------------------------------------------------------------------

STMT_KINDS = {"theorem", "lemma", "proposition", "corollary", "definition", "remark"}

def parse_latex(tex_path: Path) -> tuple[list[LatexStatement], list[LatexProofStep]]:
    """Extract formal statements and proof steps from the LaTeX source."""
    text = tex_path.read_text(encoding="utf-8")
    lines = text.splitlines()

    statements: list[LatexStatement] = []
    steps: list[LatexProofStep] = []

    current_section = ""
    # Track step numbering
    step_n = 0
    substep_n = 0
    subsubstep_n = 0
    current_parent = ""

    begin_re = re.compile(
        r"\\begin\{(" + "|".join(STMT_KINDS) + r")\}"
        r"(?:\[([^\]]*)\])?"  # optional [Title]
    )
    label_re = re.compile(r"\\label\{([^}]+)\}")
    end_re = re.compile(r"\\end\{(" + "|".join(STMT_KINDS) + r")\}")
    section_re = re.compile(r"\\section\{([^}]+)\}")

    step_re = re.compile(r"\\Step\{(.{0,120})")
    substep_re = re.compile(r"\\Substep\{(.{0,120})")
    subsubstep_re = re.compile(r"\\Subsubstep\{(.{0,120})")

    open_stmt: Optional[LatexStatement] = None

    for i, line in enumerate(lines, 1):
        # Track sections
        sm = section_re.search(line)
        if sm:
            current_section = sm.group(1).strip()
            # Reset step counters at new section/proof
            step_n = 0

        # Begin statement
        bm = begin_re.search(line)
        if bm:
            kind = bm.group(1)
            title = bm.group(2) or ""
            # Look for label on this line or next few lines
            label = ""
            lm = label_re.search(line)
            if lm:
                label = lm.group(1)
            else:
                for j in range(i, min(i + 4, len(lines))):
                    lm2 = label_re.search(lines[j])
                    if lm2:
                        label = lm2.group(1)
                        break
            stmt = LatexStatement(
                kind=kind, label=label, title=title,
                line=i, section=current_section
            )
            open_stmt = stmt
            current_parent = label or f"{kind}@L{i}"
            # Reset step counters for this proof
            step_n = 0
            substep_n = 0
            subsubstep_n = 0

        # End statement
        em = end_re.search(line)
        if em and open_stmt and em.group(1) == open_stmt.kind:
            open_stmt.end_line = i
            statements.append(open_stmt)
            open_stmt = None

        # Proof steps
        stepm = step_re.search(line)
        if stepm:
            step_n += 1
            substep_n = 0
            subsubstep_n = 0
            steps.append(LatexProofStep(
                level="Step", number=str(step_n),
                text=stepm.group(1).strip(), line=i,
                parent_statement=current_parent
            ))
        substepm = substep_re.search(line)
        if substepm:
            substep_n += 1
            subsubstep_n = 0
            steps.append(LatexProofStep(
                level="Substep", number=f"{step_n}.{substep_n}",
                text=substepm.group(1).strip(), line=i,
                parent_statement=current_parent
            ))
        subsubstepm = subsubstep_re.search(line)
        if subsubstepm:
            subsubstep_n += 1
            steps.append(LatexProofStep(
                level="Subsubstep",
                number=f"{step_n}.{substep_n}.{subsubstep_n}",
                text=subsubstepm.group(1).strip(), line=i,
                parent_statement=current_parent
            ))

    return statements, steps


def parse_lean_files(lean_dir: Path) -> list[LeanDecl]:
    """Extract declarations from all .lean files under lean_dir."""
    decls: list[LeanDecl] = []
    decl_re = re.compile(
        r"^(theorem|def|lemma|axiom|noncomputable def|abbrev|structure|instance|class)\s+"
        r"(\S+)"
    )
    sorry_re = re.compile(r"\bsorry\b")

    for lean_file in sorted(lean_dir.rglob("*.lean")):
        if ".lake" in str(lean_file):
            continue
        rel = str(lean_file.relative_to(lean_dir.parent.parent))
        text = lean_file.read_text(encoding="utf-8")
        file_lines = text.splitlines()
        for i, line in enumerate(file_lines, 1):
            dm = decl_re.match(line.strip())
            if dm:
                kind_raw = dm.group(1)
                name = dm.group(2).rstrip(" :{(")
                kind = kind_raw.replace("noncomputable ", "")
                is_axiom = kind == "axiom"
                # Check for sorry in the body (scan until next decl or EOF)
                has_sorry = False
                if not is_axiom:
                    for j in range(i, min(i + 80, len(file_lines))):
                        if sorry_re.search(file_lines[j]):
                            has_sorry = True
                            break
                        # Stop at next top-level decl
                        if j > i and decl_re.match(file_lines[j].strip()):
                            break
                decls.append(LeanDecl(
                    kind=kind, name=name, file=rel, line=i,
                    has_sorry=has_sorry, has_proof=not is_axiom
                ))
    return decls


def parse_concordance(conc_path: Path) -> list[ConcordanceEntry]:
    """Parse the concordance.md table rows."""
    entries: list[ConcordanceEntry] = []
    if not conc_path.exists():
        return entries
    text = conc_path.read_text(encoding="utf-8")
    # Match table rows: | paper result | lines | lean file | lean name | status |
    row_re = re.compile(
        r"\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|"
    )
    for line in text.splitlines():
        m = row_re.match(line)
        if m:
            paper = m.group(1).strip()
            lines_ref = m.group(2).strip()
            lean_file = m.group(3).strip()
            lean_name = m.group(4).strip()
            status = m.group(5).strip()
            # Skip header/separator rows
            if paper.startswith("---") or paper.startswith("Paper") or paper.startswith("Lean"):
                continue
            if lean_file.startswith("---"):
                continue
            entries.append(ConcordanceEntry(
                paper_result=paper, paper_lines=lines_ref,
                lean_file=lean_file, lean_name=lean_name, status=status
            ))
    return entries

# ---------------------------------------------------------------------------
# Validation logic
# ---------------------------------------------------------------------------

def validate(repo_root: Path) -> ValidationReport:
    """Run all cross-validation checks."""
    report = ValidationReport()

    tex_path = repo_root / "lamportform.tex"
    lean_dir = repo_root / "ConnesLean" / "ConnesLean"
    conc_path = repo_root / "docs" / "concordance.md"

    if not tex_path.exists():
        report.warnings.append(f"LaTeX file not found: {tex_path}")
        return report

    # Parse sources
    report.latex_statements, report.latex_steps = parse_latex(tex_path)
    if lean_dir.exists():
        report.lean_decls = parse_lean_files(lean_dir)
    report.concordance = parse_concordance(conc_path)

    # Build lookup sets
    concordance_lean_names: set[str] = set()
    concordance_statuses: dict[str, str] = {}
    formalized_labels: set[str] = set()

    for entry in report.concordance:
        for name in re.split(r"[,`]", entry.lean_name):
            name = name.strip().strip("`")
            if name:
                concordance_lean_names.add(name)
        status_lower = entry.status.strip("*").strip().lower()
        concordance_statuses[entry.paper_result] = status_lower

    # Map concordance entries back to LaTeX labels where possible
    label_to_concordance: dict[str, list[ConcordanceEntry]] = {}
    for entry in report.concordance:
        # Try to extract label-like references from paper_result
        for lbl_candidate in re.findall(r"(?:Lemma|Theorem|Proposition|Corollary|Definition|Remark)\s+\d+", entry.paper_result):
            label_to_concordance.setdefault(lbl_candidate, []).append(entry)

    # 1. Find unformalized LaTeX statements
    #    Check if each statement has a concordance entry with status != "not yet"
    for stmt in report.latex_statements:
        # Skip remarks (often commentary, not formal results)
        # but include them in the checklist
        is_covered = False
        for entry in report.concordance:
            # Match by line range
            if entry.paper_lines.strip() == "—":
                continue
            try:
                line_parts = entry.paper_lines.replace("–", "-").split("-")
                if len(line_parts) >= 1:
                    start = int(line_parts[0].strip())
                    end = int(line_parts[-1].strip()) if len(line_parts) > 1 else start
                    if start <= stmt.line <= end or stmt.line <= start <= (stmt.end_line or stmt.line + 50):
                        status = entry.status.strip("*").strip().lower()
                        if status in ("proved", "axiom"):
                            is_covered = True
                            break
            except (ValueError, IndexError):
                continue
        if not is_covered:
            report.unformalized.append(stmt)

    # 2. Find axioms
    report.axioms = [d for d in report.lean_decls if d.kind == "axiom"]

    # 3. Find sorry declarations
    report.sorry_decls = [d for d in report.lean_decls if d.has_sorry]

    # 4. Find Lean declarations not tracked in concordance
    tracked_names = set()
    for entry in report.concordance:
        for name in re.split(r"[,`\s]+", entry.lean_name):
            name = name.strip().strip("`")
            if name:
                tracked_names.add(name)
    # Only flag non-trivial declarations (skip instances, helpers)
    interesting_kinds = {"theorem", "def", "lemma", "axiom", "structure", "abbrev"}
    for decl in report.lean_decls:
        if decl.kind in interesting_kinds and decl.name not in tracked_names:
            # Skip internal helpers (names starting with lowercase or containing _aux)
            if not decl.name[0].isupper() and "_" in decl.name:
                # Still include it — reviewer can decide
                pass
            report.untracked_lean.append(decl)

    # 5. Consistency warnings
    # Check for axioms whose paper reference claims "proved"
    for entry in report.concordance:
        status = entry.status.strip("*").strip().lower()
        if status == "proved":
            for name in re.split(r"[,`\s]+", entry.lean_name):
                name = name.strip().strip("`")
                for decl in report.lean_decls:
                    if decl.name == name and decl.kind == "axiom":
                        report.warnings.append(
                            f"Concordance says '{entry.paper_result}' is **proved** "
                            f"but `{name}` is declared as axiom in {decl.file}:{decl.line}"
                        )

    # Check for axiom count drift
    n_axioms = len(report.axioms)
    if n_axioms > 10:
        report.warnings.append(
            f"Axiom count ({n_axioms}) exceeds threshold of 10 — review for eliminable axioms"
        )

    return report

# ---------------------------------------------------------------------------
# Output formatting
# ---------------------------------------------------------------------------

def format_report(report: ValidationReport, checklist_only: bool = False) -> str:
    """Format the validation report as Markdown."""
    out: list[str] = []

    def heading(level: int, text: str) -> None:
        out.append(f"\n{'#' * level} {text}\n")

    def bullet(text: str) -> None:
        out.append(f"- {text}")

    # Header
    out.append("# LaTeX–Lean Validation Report")
    out.append("")
    out.append(f"Generated from `lamportform.tex` ({len(report.latex_statements)} formal statements, "
               f"{len(report.latex_steps)} proof steps) and "
               f"`ConnesLean/` ({len(report.lean_decls)} Lean declarations).")
    out.append("")

    # Summary statistics
    if not checklist_only:
        heading(2, "Summary")
        n_proved = sum(1 for e in report.concordance if "proved" in e.status.lower())
        n_axiom_conc = sum(1 for e in report.concordance if "axiom" in e.status.lower())
        n_not_yet = sum(1 for e in report.concordance if "not yet" in e.status.lower())
        out.append(f"| Metric | Count |")
        out.append(f"|--------|-------|")
        out.append(f"| LaTeX formal statements | {len(report.latex_statements)} |")
        out.append(f"| LaTeX proof steps | {len(report.latex_steps)} |")
        out.append(f"| Lean declarations | {len(report.lean_decls)} |")
        out.append(f"| Concordance: proved | {n_proved} |")
        out.append(f"| Concordance: axiom | {n_axiom_conc} |")
        out.append(f"| Concordance: not yet | {n_not_yet} |")
        out.append(f"| Lean axiom declarations | {len(report.axioms)} |")
        out.append(f"| Lean sorry occurrences | {len(report.sorry_decls)} |")
        out.append(f"| Untracked Lean decls | {len(report.untracked_lean)} |")
        out.append("")

    # Warnings
    if report.warnings and not checklist_only:
        heading(2, "Warnings")
        for w in report.warnings:
            bullet(w)
        out.append("")

    # Unformalized LaTeX statements
    if not checklist_only:
        heading(2, "Unformalized LaTeX Statements")
        if report.unformalized:
            out.append("These LaTeX statements have no matching concordance entry with status 'proved' or 'axiom':")
            out.append("")
            out.append("| Kind | Title | Label | Line | Section |")
            out.append("|------|-------|-------|------|---------|")
            for stmt in report.unformalized:
                title = stmt.title[:60] + ("..." if len(stmt.title) > 60 else "")
                label = f"`{stmt.label}`" if stmt.label else "—"
                section = stmt.section[:40] + ("..." if len(stmt.section) > 40 else "")
                out.append(f"| {stmt.kind} | {title} | {label} | {stmt.line} | {section} |")
            out.append("")
        else:
            out.append("All formal statements have concordance entries.")
            out.append("")

    # Axioms
    if not checklist_only:
        heading(2, "Axioms (Trusted, Not Machine-Checked)")
        if report.axioms:
            out.append("| Name | File | Line |")
            out.append("|------|------|------|")
            for ax in report.axioms:
                out.append(f"| `{ax.name}` | `{ax.file}` | {ax.line} |")
            out.append("")
        else:
            out.append("No axioms found.")
            out.append("")

    # Sorry declarations
    if not checklist_only and report.sorry_decls:
        heading(2, "Declarations Containing `sorry`")
        out.append("| Name | File | Line |")
        out.append("|------|------|------|")
        for d in report.sorry_decls:
            out.append(f"| `{d.name}` | `{d.file}` | {d.line} |")
        out.append("")

    # Untracked Lean declarations
    if not checklist_only and report.untracked_lean:
        heading(2, "Lean Declarations Not in Concordance")
        out.append("These declarations are not mentioned in `docs/concordance.md`. "
                    "They may be helpers, or they may need to be added.")
        out.append("")
        out.append("| Kind | Name | File | Line |")
        out.append("|------|------|------|------|")
        for d in report.untracked_lean:
            out.append(f"| {d.kind} | `{d.name}` | `{d.file}` | {d.line} |")
        out.append("")

    # -------------------------------------------------------------------
    # Human Review Checklist
    # -------------------------------------------------------------------
    heading(2, "Human Review Checklist")
    out.append("Use this checklist to guide a systematic review of the formalization "
               "against the LaTeX source.\n")

    # Group by LaTeX section
    sections: dict[str, list[LatexStatement]] = {}
    for stmt in report.latex_statements:
        sec = stmt.section or "(no section)"
        sections.setdefault(sec, []).append(stmt)

    # Build concordance lookup by line overlap
    def concordance_for_stmt(stmt: LatexStatement) -> list[ConcordanceEntry]:
        matches = []
        for entry in report.concordance:
            if entry.paper_lines.strip() == "—":
                continue
            try:
                parts = entry.paper_lines.replace("–", "-").split("-")
                start = int(parts[0].strip())
                end = int(parts[-1].strip()) if len(parts) > 1 else start
                if (start <= stmt.line <= end) or (stmt.line <= start <= (stmt.end_line or stmt.line + 100)):
                    matches.append(entry)
            except (ValueError, IndexError):
                continue
        return matches

    axiom_names = {d.name for d in report.axioms}

    for sec_name, stmts in sections.items():
        heading(3, sec_name)
        for stmt in stmts:
            entries = concordance_for_stmt(stmt)
            title_str = f" — {stmt.title}" if stmt.title else ""
            label_str = f" (`{stmt.label}`)" if stmt.label else ""

            # Determine status
            if entries:
                statuses = {e.status.strip("*").strip().lower() for e in entries}
                if "not yet" in statuses:
                    status_icon = "[ ]"
                elif "axiom" in statuses:
                    status_icon = "[~]"  # partially trusted
                else:
                    status_icon = "[x]"
            else:
                status_icon = "[ ]"

            out.append(f"- {status_icon} **{stmt.kind.title()} (L{stmt.line})**{title_str}{label_str}")

            if entries:
                for entry in entries:
                    s = entry.status.strip("*").strip().lower()
                    icon = {"proved": "proved", "axiom": "AXIOM", "not yet": "NOT YET"}.get(s, s)
                    out.append(f"  - Lean: `{entry.lean_name}` ({icon})")
            else:
                out.append(f"  - **No Lean counterpart found** — needs formalization or concordance update")

            # Sub-checklist items for review
            out.append(f"  - [ ] Statement matches LaTeX claim (line {stmt.line})")
            out.append(f"  - [ ] Hypotheses match (no missing or extra assumptions)")
            if entries:
                for entry in entries:
                    for name in re.split(r"[,`\s]+", entry.lean_name):
                        name = name.strip().strip("`")
                        if name in axiom_names:
                            out.append(f"  - [ ] Axiom `{name}`: soundness annotation reviewed")
            # Check if there are proof steps for this statement
            stmt_id = stmt.label or f"{stmt.kind}@L{stmt.line}"
            child_steps = [s for s in report.latex_steps if s.parent_statement == stmt_id]
            if child_steps:
                out.append(f"  - [ ] Proof structure ({len(child_steps)} steps) — spot-check key steps:")
                for step in child_steps[:8]:  # Show first 8
                    text_preview = step.text[:80].replace("|", "\\|")
                    out.append(f"    - [ ] {step.level} {step.number} (L{step.line}): {text_preview}")
                if len(child_steps) > 8:
                    out.append(f"    - ... and {len(child_steps) - 8} more steps")

        out.append("")

    # Global checks
    heading(3, "Global Checks")
    out.append("- [ ] No `sorry` in any merged Lean file")
    out.append("- [ ] All axioms have `**Soundness:**` docstring annotations")
    out.append("- [ ] Axiom count is within expected bounds "
               f"(currently {len(report.axioms)})")
    out.append("- [ ] CI passes: `lake build ConnesLean` succeeds")
    out.append("- [ ] Concordance (`docs/concordance.md`) is up to date")
    out.append("- [ ] No unexpected `maxHeartbeats` overrides")
    out.append("")

    # Step coverage summary
    heading(3, "Proof Step Coverage")
    total_steps = len(report.latex_steps)
    out.append(f"The LaTeX document contains **{total_steps}** structured proof steps "
               f"across **{len(report.latex_statements)}** formal statements.")
    out.append("")
    # Group steps by parent
    step_groups: dict[str, list[LatexProofStep]] = {}
    for step in report.latex_steps:
        step_groups.setdefault(step.parent_statement, []).append(step)
    out.append("| Parent Statement | Steps | Top-level | Sub | Sub-sub |")
    out.append("|------------------|-------|-----------|-----|---------|")
    for parent, psteps in step_groups.items():
        n_top = sum(1 for s in psteps if s.level == "Step")
        n_sub = sum(1 for s in psteps if s.level == "Substep")
        n_subsub = sum(1 for s in psteps if s.level == "Subsubstep")
        out.append(f"| `{parent}` | {len(psteps)} | {n_top} | {n_sub} | {n_subsub} |")
    out.append("")

    return "\n".join(out)

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Cross-validate LaTeX source against Lean formalization"
    )
    parser.add_argument(
        "-o", "--output", type=str, default=None,
        help="Write report to this file instead of stdout"
    )
    parser.add_argument(
        "--checklist-only", action="store_true",
        help="Only output the human review checklist section"
    )
    parser.add_argument(
        "--repo-root", type=str, default=None,
        help="Repository root (default: auto-detect from script location)"
    )
    args = parser.parse_args()

    if args.repo_root:
        repo_root = Path(args.repo_root)
    else:
        repo_root = Path(__file__).resolve().parent.parent

    report = validate(repo_root)
    text = format_report(report, checklist_only=args.checklist_only)

    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
        print(f"Report written to {args.output}", file=sys.stderr)
    else:
        print(text)


if __name__ == "__main__":
    main()
