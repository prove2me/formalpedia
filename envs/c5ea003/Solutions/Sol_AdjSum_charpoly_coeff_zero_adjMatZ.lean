-- Prove2me | solution 1 for AdjSum.charpoly_coeff_zero_adjMatZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:26:43.269837+00:00
-- url     : https://prove2.me/submissions/83a57936-f0ef-4cca-b3c9-f601fe0d5a60

-- Sol generated from Applications/AdjacentSumPolytopes/Determinant.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence
import Theorems.Thm_AdjSum_det_adjMatZ

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

/-- Powers of `-1` only depend on the exponent modulo `2`. -/
lemma neg_one_pow_eq_of_mod_two {a b : ℕ} (h : a % 2 = b % 2) :
    ((-1 : ℤ)) ^ a = ((-1 : ℤ)) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := b), h]

/-- The parity bookkeeping behind the closed form of the determinant. -/
lemma mod_two_step (s : ℕ) : (s + 1 + (s + 1) / 2) % 2 = ((s + 2) / 2) % 2 := by
  rcases Nat.even_or_odd s with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm
  · have h1 : (m + m + 1) / 2 = m := by omega
    have h2 : (m + m + 2) / 2 = m + 1 := by omega
    rw [h1, h2]
    omega
  · have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 1 + 2) / 2 = m + 1 := by omega
    rw [h1, h2]
    omega






open AdjSum in
theorem solution(s : ℕ) :
    (adjMatZ s).charpoly.coeff 0 = (-1) ^ ((s + 2) / 2) := by
  have hdet := Matrix.det_eq_sign_charpoly_coeff (adjMatZ s)
  rw [det_adjMatZ, Fintype.card_fin] at hdet
  have hunit : ((-1 : ℤ)) ^ (s + 1) * ((-1 : ℤ)) ^ (s + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hval : (adjMatZ s).charpoly.coeff 0
      = ((-1 : ℤ)) ^ (s + 1) * ((-1 : ℤ)) ^ ((s + 1) / 2) := by
    calc (adjMatZ s).charpoly.coeff 0 = 1 * (adjMatZ s).charpoly.coeff 0 := (one_mul _).symm
      _ = ((-1 : ℤ)) ^ (s + 1) * (((-1 : ℤ)) ^ (s + 1) * (adjMatZ s).charpoly.coeff 0) := by
          rw [← mul_assoc, hunit, one_mul]
      _ = ((-1 : ℤ)) ^ (s + 1) * ((-1 : ℤ)) ^ ((s + 1) / 2) := by rw [← hdet]
  rw [hval, ← pow_add]
  exact neg_one_pow_eq_of_mod_two (mod_two_step s)
