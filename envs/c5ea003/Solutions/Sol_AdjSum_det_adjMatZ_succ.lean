-- Prove2me | solution 1 for AdjSum.det_adjMatZ_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:22:39.764299+00:00
-- url     : https://prove2.me/submissions/bdeeb6bf-e94d-453e-9cd3-c32e241cd55f

-- Sol generated from Applications/AdjacentSumPolytopes/Determinant.lean
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








open AdjSum in
theorem solution(s : ℕ) :
    (adjMatZ (s + 1)).det = (-1) ^ (s + 1) * (adjMatZ s).det := by
  rw [Matrix.det_succ_row (adjMatZ (s + 1)) (Fin.last (s + 1))]
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (s + 2))), j ≠ 0 →
      (-1) ^ ((Fin.last (s + 1) : Fin (s + 2)) : ℕ) ^ 0 * (0 : ℤ) = 0 := by
    intro j _ _
    ring
  rw [Finset.sum_eq_single (0 : Fin (s + 2))]
  · have hentry : adjMatZ (s + 1) (Fin.last (s + 1)) 0 = 1 := by
      simp [adjMatZ]
    have hsub : (adjMatZ (s + 1)).submatrix (Fin.last (s + 1)).succAbove
        ((0 : Fin (s + 2)).succAbove) = adjMatZ s := by
      ext a b
      rw [Matrix.submatrix_apply, Fin.succAbove_last, Fin.zero_succAbove]
      simp only [adjMatZ, Fin.val_castSucc, Fin.val_succ]
      by_cases h : (a : ℕ) + (b : ℕ) ≤ s
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [hentry, hsub]
    simp
  · intro j _ hj
    have hval : (j : ℕ) ≠ 0 := by
      intro hc
      exact hj (Fin.ext (by simpa using hc))
    have hentry : adjMatZ (s + 1) (Fin.last (s + 1)) j = 0 := by
      simp only [adjMatZ, Fin.val_last]
      rw [if_neg (by omega)]
    rw [hentry]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h
