-- Prove2me | Theorems.Thm_AdjSum_det_adjMatZ
-- name    : AdjSum.det_adjMatZ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:12:45.478548+00:00
-- url     : https://prove2.me/theorems/53d15eeb-b04e-4bf5-8563-200d22fe9c3f
-- title:
--   Unimodularity in closed form.
-- statement:
--   **Unimodularity in closed form.**  `det(adjMat s) = (−1)^{⌊(s+1)/2⌋}`.
--
--   ```lean
--   theorem AdjSum.det_adjMatZ(s : ℕ) : (adjMatZ s).det = (-1) ^ ((s + 1) / 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/Determinant.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/Determinant.lean#L96

-- Thm stub generated from Applications/AdjacentSumPolytopes/Determinant.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# The transfer matrix is unimodular

The last row of the adjacent-sum transfer matrix is the unit vector `e₀` (only `b = 0`
satisfies `s + b ≤ s`), and deleting that row together with the first column shifts the
model down by one unit of slack.  Laplace expansion along the last row therefore gives the
one-step recurrence

`det(adjMat (s+1)) = (−1)^{s+1} · det(adjMat s)`,

whence the closed form `det(adjMat s) = (−1)^{⌊(s+1)/2⌋}`: the transfer matrix is
**unimodular** for every slack, with a period-four sign pattern `+, −, −, +`.

This settles sub-conjecture (S2) of `FUTURE_DIRECTIONS.md` and, via
`Matrix.det_eq_sign_charpoly_coeff`, the `m = s + 1` (constant-term) case of the binomial
staircase Conjecture 1, whose prediction there is `(−1)^{⌊(s+2)/2⌋}·C(s+1, s+1)`.

## Main results

* `AdjSum.det_adjMatZ_succ` : the Laplace recurrence `det A_{s+1} = (−1)^{s+1} det A_s`.
* `AdjSum.det_adjMatZ` : `det(adjMat s) = (−1)^{⌊(s+1)/2⌋}`.
* `AdjSum.isUnit_det_adjMatZ` : unimodularity, hence invertibility over `ℤ`.
* `AdjSum.charpoly_coeff_zero_adjMatZ` : the constant term of the characteristic
  polynomial is `(−1)^{⌊(s+2)/2⌋}`, the `m = s+1` case of the binomial conjecture.

-- !-- Lab Notes -- !--
* **Experiment.** `det(adjMat s)` for `s = 0..9` is `1, −1, −1, 1, 1, −1, −1, 1, 1, −1`,
  matching `(−1)^{⌊(s+1)/2⌋}` and the constant terms of the characteristic polynomials
  tabulated in `ComputationalEvidence.md` §2.
* **Analysis.** The recurrence is *not* a similarity: it changes the size of the matrix,
  and the sign `(−1)^{s+1}` is exactly the Laplace cofactor sign of the corner entry.  The
  period-four pattern is the parity of `s(s+1)/2`, i.e. the sign of the reversal
  permutation of `s+1` letters — consistent with `A_s = P_rev · L` for the lower
  unitriangular `L`.
* **Critique.** Unimodularity is what makes every `2×2` window of `Mⁿ` have determinant
  `±1`, which is the Catalan-type input required by Conjecture 4 (arctangent closed forms
  beyond `s = 1`); it is stated over `ℤ` so that no division is involved.
-/

open AdjSum

open Finset

theorem AdjSum.det_adjMatZ(s : ℕ) : (adjMatZ s).det = (-1) ^ ((s + 1) / 2) := by sorry
