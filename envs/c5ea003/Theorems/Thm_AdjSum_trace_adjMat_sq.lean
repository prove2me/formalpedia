-- Prove2me | Theorems.Thm_AdjSum_trace_adjMat_sq
-- name    : AdjSum.trace_adjMat_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:15:05.057953+00:00
-- url     : https://prove2.me/theorems/a3236bb7-0d18-4514-bf52-f767f11411a7
-- title:
--   The second trace moment.
-- statement:
--   **The second trace moment.**  `tr(A²)` is the triangular number `C(s+2, 2)`.
--
--   ```lean
--   theorem AdjSum.trace_adjMat_sq(s : ℕ) : Matrix.trace (adjMat s ^ 2) = Nat.choose (s + 2) 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/TraceMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/TraceMoments.lean#L71

-- Thm stub generated from Applications/AdjacentSumPolytopes/TraceMoments.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace

/-!
# The second trace moment and the Newton coefficient `e₂`

`Necklace.trace_adjMat` computed the first trace moment, `tr(A) = ⌊s/2⌋ + 1`, which is the
`m = 1` coefficient of the characteristic polynomial.  This file computes the second
moment exactly,

`tr(A²) = C(s+2, 2)`,

i.e. the number of cyclic adjacent-sum lattice points of length `2` is a triangular
number, and derives the second elementary symmetric function of the spectrum in closed
form via Newton's identity `2e₂ = e₁² − p₂`:

`e₂ = − C(⌊(s+3)/2⌋, 2)`.

This is the `m = 2` instance of the binomial conjecture recorded in `FUTURE_DIRECTIONS.md`
(coefficient of `x^{s+1−m}` in `det(xI − A)` equals
`(−1)^{⌊(m+1)/2⌋} C(⌊(s+1+m)/2⌋, m)`); the `m = 0, 1` instances are `1` and `−tr(A)`, both
already proved.

## Main results

* `AdjSum.trace_adjMat_sq` : `tr(A²) = C(s+2, 2)`.
* `AdjSum.cycCount_one_eq_choose` : the length-`2` cyclic count is `C(s+2, 2)`.
* `AdjSum.trace_sq_newton` : `tr(A²) = tr(A)² + 2·C(⌊(s+3)/2⌋, 2)`, the Newton relation
  that pins down `e₂`.

-- !-- Lab Notes -- !--
* **Experiment.** `tr(A²)` for `s = 0..9` is `1, 3, 6, 10, 15, 21, 28, 36, 45, 55`, exactly
  the triangular numbers `C(s+2,2)`; `tr(A)` is `1, 1, 2, 2, 3, 3, 4, 4, 5, 5`, and the
  differences `tr(A²) − tr(A)²` are `0, 2, 2, 6, 6, 12, 12, 20, 20, 30`, i.e.
  `2·C(⌊(s+3)/2⌋, 2)`.
* **Analysis.** The parity-dependent floor in `e₂` is the first place where the two parity
  classes of the model separate at the level of the characteristic polynomial, which is
  why the conjectured coefficient formula needs `⌊(s+1+m)/2⌋` rather than a polynomial in
  `s`.
* **Critique.** The identity is proved as a natural-number identity, so no division is
  hidden: `Nat.choose` is used instead of `(s+1)(s+2)/2`, and the parity split is
  discharged by `omega` after `Nat.choose_two_right`.
-/

open AdjSum

open Finset

theorem AdjSum.trace_adjMat_sq(s : ℕ) : Matrix.trace (adjMat s ^ 2) = Nat.choose (s + 2) 2 := by sorry
