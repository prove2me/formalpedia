-- Prove2me | solution 1 for mme_boundary_volume_entropy_log_lower
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:13:25.564888+00:00
-- url     : https://prove2.me/submissions/3a39c13f-f3b7-4103-8bde-9b1c6dc79f75

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false

/-- The boundary volume retains the full histogram entropy, with an explicit
logarithmic loss, together with the contribution of the nonzero CW letters. -/
theorem solution {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) :
    (L : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) -
      (Fintype.card (CompleteWord ell) : ℝ) * Real.log (6 * ((L + 1 : ℕ) : ℝ)) +
      ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5 ≤
        Real.log (B.dim : ℝ) := by
  classical
  have hmass : 0 < ∑ s, B.count s := by rw [B.total]; exact hL
  have h := mme_dwz_multinomial_entropy_polynomial_lower
    B.count 1 (by decide) hmass
  simp only [Nat.mul_one, B.total] at h
  have hm : (0 : ℝ) < Nat.multinomial Finset.univ B.count := by
    exact_mod_cast Nat.multinomial_pos Finset.univ B.count
  have hp : (0 : ℝ) < 6 * ((L + 1 : ℕ) : ℝ) := by positivity
  have hl := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_mul (ne_of_gt (pow_pos hp _)) (ne_of_gt hm),
    Real.log_pow] at hl
  have hd : (B.dim : ℝ) =
      (Nat.multinomial Finset.univ B.count : ℝ) *
        (5 : ℝ) ^ (∑ s, B.count s * ones s) := by
    simp only [Profile.dim, Nat.multinomial, B.total, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hd, Real.log_mul (ne_of_gt hm) (by positivity), Real.log_pow]
  linarith


#print axioms solution
