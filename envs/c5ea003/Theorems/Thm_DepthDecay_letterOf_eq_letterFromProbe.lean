-- Prove2me | Theorems.Thm_DepthDecay_letterOf_eq_letterFromProbe
-- name    : DepthDecay.letterOf_eq_letterFromProbe
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:47:38.126236+00:00
-- url     : https://prove2.me/theorems/267a33ca-403d-44b8-9f72-20ed59142275
-- title:
--   Depth-1 readability.
-- statement:
--   **Depth-1 readability.**  For every admissible state the first descent letter
--   is an explicit function of the one-bit magnitude probe `⌊2m/n⌋`.  This is the
--   formal content of "the magnitude channel exists".
--
--   ```lean
--   theorem DepthDecay.letterOf_eq_letterFromProbe{s : ℕ × ℕ} (h : Adm s) :
--       letterOf s = letterFromProbe (probe 1 s) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/WindowSensor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/WindowSensor.lean#L173

-- Thm stub generated from Cryptography/DepthDecay/WindowSensor.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

/-!
# Depth decay of the magnitude channel on the Berggren / Pythagorean tree

## Setting

Primitive Pythagorean triples are in bijection with *admissible pairs* `(m, n)` of
naturals: `0 < n < m`, `gcd m n = 1`, `m + n` odd.  Berggren's ternary tree on
primitive triples becomes, in these coordinates, the ternary tree on admissible
pairs with children

* `A : (m, n) ↦ (2m - n, m)`,
* `B : (m, n) ↦ (2m + n, m)`,
* `C : (m, n) ↦ (m + 2n, n)`,

rooted at `(2,1)` (the triple `(3,4,5)`).  Inverting, every non-root admissible
pair has a unique *parent*, and which of the three inverse branches applies is
decided purely by the position of the **ratio** `r = m/n` relative to the two
cut points `2` and `3`:

* `r < 2`     → letter `A`, parent `(n, 2n - m)` (parent ratio `1/(2-r)`),
* `2 < r < 3` → letter `B`, parent `(n, m - 2n)` (parent ratio `1/(r-2)`),
* `3 < r`     → letter `C`, parent `(m - 2n, n)` (parent ratio `r - 2`).

This is a Gauss-map style digit expansion of the ratio `r`.

## The sensor model

A *W-window sensor* is the computable functional `probe W (m,n) = ⌊2^W · m / n⌋`:
it reads the magnitude of the ratio to `W` binary places and nothing else, with
a budget independent of the depth of the state in the tree.  This file proves
exactly how far down the descent such a sensor can see.

## Main results (this file)

* `letterOf_eq_letterFromProbe` : the **first** letter is an explicit function of
  the one-bit probe `⌊2m/n⌋`.  The magnitude channel really exists at depth 1.
* `probe_one_parent_of_C` : along a `C`-step the probe merely shifts by `4`.
* `letterAt_eq_of_probe_one_of_prefix_C` : if two admissible states share the
  one-bit probe, then all of their letters agree up to *and including* the first
  non-`C` letter.  The readable prefix is the leading `C`-run plus one inversion
  letter.
* `cRun_letters_C`, `cRun_letterAt_ne_C` : the length of that leading `C`-run is
  the single integer division `(m - n) / (2n)`; depth itself is therefore visible
  to the magnitude channel.

The complementary **null** result — no fixed window can read the letter
immediately after the first inversion, at any prescribed depth — is
`Cryptography.DepthDecay.NullBeyondInversion`.
-/

open DepthDecay









/-! ### Basic structure of admissible states -/





/-! ### The channel at depth one: the first letter is a magnitude readout -/

theorem DepthDecay.letterOf_eq_letterFromProbe{s : ℕ × ℕ} (h : Adm s) :
    letterOf s = letterFromProbe (probe 1 s) := by sorry
