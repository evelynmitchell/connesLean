#!/usr/bin/env bash
# lint_axiom_soundness.sh — Verify every axiom has a **Soundness:** annotation
# and is tracked in the soundness inventory.
#
# Exit codes: 0 = all checks pass, 1 = failures found.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_DIR="$REPO_ROOT/ConnesLean"
SOUNDNESS_FILE="$LEAN_DIR/soundness/Main.lean"
MAX_LOOKBACK=40
ERRORS=0

# Collect all axiom declarations (file:line:content)
# Match axioms at line start, possibly preceded by whitespace.
mapfile -t AXIOM_LINES < <(
  grep -rn '^\s*axiom ' "$LEAN_DIR" --include='*.lean' \
    --exclude-dir='.lake' --exclude-dir='soundness'
)

if [ ${#AXIOM_LINES[@]} -eq 0 ]; then
  echo "No axiom declarations found."
  exit 0
fi

echo "=== Axiom Soundness Lint ==="
echo "Found ${#AXIOM_LINES[@]} axiom declaration(s)."
echo ""

# Lean declaration keywords used as backward-scan boundaries
DECL_BOUNDARY='^(axiom |theorem |def |lemma |instance |abbrev |structure |class |noncomputable |private |protected )'

# ── Check 1 & 2: Soundness annotation and docstring presence ──
for entry in "${AXIOM_LINES[@]}"; do
  FILE="$(echo "$entry" | cut -d: -f1)"
  LINE_NUM="$(echo "$entry" | cut -d: -f2)"
  AXIOM_TEXT="$(echo "$entry" | cut -d: -f3-)"
  # Extract name: strip leading whitespace and "axiom " prefix, then take first word
  AXIOM_NAME="${AXIOM_TEXT#"${AXIOM_TEXT%%[![:space:]]*}"}"
  AXIOM_NAME="${AXIOM_NAME#axiom }"
  AXIOM_NAME="${AXIOM_NAME%% *}"
  AXIOM_NAME="${AXIOM_NAME%%(*}"

  HAS_SOUNDNESS=false
  HAS_DOCSTRING=false
  IN_DOCSTRING=false
  START=$((LINE_NUM - MAX_LOOKBACK))
  [ "$START" -lt 1 ] && START=1

  # Scan backwards from the line before the axiom.
  # Only count **Soundness:** markers found inside the docstring (after seeing -/).
  for (( i = LINE_NUM - 1; i >= START; i-- )); do
    SCAN_LINE="$(sed -n "${i}p" "$FILE")"

    # Entering the docstring from its closing end
    if ! $IN_DOCSTRING && echo "$SCAN_LINE" | grep -q '\-/'; then
      IN_DOCSTRING=true
    fi

    # Check for **Soundness:** marker — only if inside the docstring
    if $IN_DOCSTRING && echo "$SCAN_LINE" | grep -q '\*\*Soundness:\*\*'; then
      HAS_SOUNDNESS=true
    fi

    # Check for docstring open
    if echo "$SCAN_LINE" | grep -q '/--'; then
      HAS_DOCSTRING=true
      break
    fi

    # Stop at previous declaration boundary (only before entering docstring)
    if ! $IN_DOCSTRING && echo "$SCAN_LINE" | grep -qE "$DECL_BOUNDARY"; then
      break
    fi
  done

  # Report Check 2: docstring presence
  if ! $HAS_DOCSTRING; then
    echo "FAIL [docstring]: $AXIOM_NAME ($FILE:$LINE_NUM) — no preceding /-- docstring"
    ERRORS=$((ERRORS + 1))
  fi

  # Report Check 1: soundness annotation
  if ! $HAS_SOUNDNESS; then
    echo "FAIL [soundness]: $AXIOM_NAME ($FILE:$LINE_NUM) — missing **Soundness:** annotation"
    ERRORS=$((ERRORS + 1))
  fi
done

echo ""

# ── Check 3: Inventory sync ──
echo "--- Inventory sync ---"

# Extract axiom names from source files (short names, no namespace prefix)
mapfile -t SOURCE_AXIOMS < <(
  for entry in "${AXIOM_LINES[@]}"; do
    TEXT="$(echo "$entry" | cut -d: -f3-)"
    NAME="${TEXT#"${TEXT%%[![:space:]]*}"}"
    NAME="${NAME#axiom }"
    NAME="${NAME%% *}"
    NAME="${NAME%%(*}"
    echo "$NAME"
  done | sort
)

# Extract axiom names from knownProjectAxioms in soundness/Main.lean
mapfile -t INVENTORY_AXIOMS < <(
  grep '`ConnesLean\.' "$SOUNDNESS_FILE" \
    | sed 's/.*`ConnesLean\.\([^ ,]*\).*/\1/' \
    | sort
)

# Check source axioms present in inventory
for ax in "${SOURCE_AXIOMS[@]}"; do
  FOUND=false
  for inv in "${INVENTORY_AXIOMS[@]}"; do
    if [ "$ax" = "$inv" ]; then
      FOUND=true
      break
    fi
  done
  if ! $FOUND; then
    echo "FAIL [inventory]: $ax is in source but missing from knownProjectAxioms"
    ERRORS=$((ERRORS + 1))
  fi
done

# Check inventory entries present in source
for inv in "${INVENTORY_AXIOMS[@]}"; do
  FOUND=false
  for ax in "${SOURCE_AXIOMS[@]}"; do
    if [ "$inv" = "$ax" ]; then
      FOUND=true
      break
    fi
  done
  if ! $FOUND; then
    echo "FAIL [inventory]: $inv is in knownProjectAxioms but not found in source"
    ERRORS=$((ERRORS + 1))
  fi
done

echo ""

# ── Summary ──
if [ "$ERRORS" -gt 0 ]; then
  echo "FAILED: $ERRORS error(s) found."
  exit 1
else
  echo "OK: All ${#AXIOM_LINES[@]} axiom(s) have docstrings, **Soundness:** annotations, and inventory entries."
  exit 0
fi
