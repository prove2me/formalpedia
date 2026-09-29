-- Prove2me | solution 1 for mme_CW_q6_coupled_scalar_value_below
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T08:13:56.532444+00:00
-- url     : https://prove2.me/submissions/7a67d31e-5daa-4cc7-ab1f-3d1f27f2cc87

import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
import Theorems.Thm_mme_MMObj_square_scalar_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Mathlib.Tactic

open MME Filter
universe u
set_option autoImplicit false

/-- Uniform square extractions at exponent two thirds yield scalar value
independent of the exponent. -/
theorem solution
    {K : Type u} [Field K] (tau V : ℝ) (hV : 0 ≤ V) (hVlt : V < 5472) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V := by
  let W : ℝ := (V + 5472) / 2
  have hVW : V < W := by dsimp [W]; linarith
  have hW : 0 ≤ W := hV.trans hVW.le
  have hWlt : W < 5472 := by dsimp [W]; linarith
  obtain ⟨C, hC, hextract⟩ :=
    mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
      (K := K) (2 / 3) (by norm_num)
  have hbase : 4 * (6 : ℝ) ^ (3 * (2 / 3 : ℝ)) *
      ((6 : ℝ) ^ (3 * (2 / 3 : ℝ)) + 2) = 5472 := by norm_num
  rw [hbase] at hextract
  have hsq : W ^ 2 < (5472 : ℝ) ^ 2 := by nlinarith
  have hloss := mme_strict_pow_absorbs_sqrt_exp_loss
    (W ^ 2) ((5472 : ℝ) ^ 2) C (sq_nonneg W) hsq hC
  obtain ⟨N, hN, hloss, hextract⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and (hloss.and hextract)).exists
  dsimp only at hextract
  obtain ⟨k, hr, hk⟩ := hextract
  let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * (2 / 3 : ℝ)) + 2) * (N : ℝ)⌋₊
  let side : ℕ := 6 ^ (4 * (N - L) + 2 * L)
  change TensorObj.Restrict
    (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K side side side))
    ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) at hr
  change (5472 : ℝ) ^ (2 * N) *
    Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      (k : ℝ) * (((side ^ 3 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) at hk
  have hweight : (((side ^ 3 : ℕ) : ℝ) ^ (2 / 3 : ℝ)) = (side : ℝ) ^ 2 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
    norm_num
    exact Real.rpow_two _
  rw [hweight] at hk
  rw [← pow_mul, ← pow_mul] at hloss
  have hstrict : V ^ (2 * N) < W ^ (2 * N) := by
    gcongr
  have hbudget : V ^ (2 * N) < (k : ℝ) * (side : ℝ) ^ 2 :=
    hstrict.trans_le (hloss.trans hk)
  have hsum := mme_HasTauValueAtLeast_bigAdd_uniform_strict
    (fun _ : Fin k ↦ MMObj K side side side) tau ((side : ℝ) ^ 2)
    (sq_nonneg _) (fun _ W hW hWlt ↦
      mme_MMObj_square_scalar_value_below side tau W hW hWlt)
    (V ^ (2 * N)) (pow_nonneg hV _) hbudget
  exact mme_HasTauValueAtLeast_kronPow_root
    (cyclicSymmetrization (coupledObj K 6)) tau V (2 * N)
    (by omega) hV (mme_HasTauValueAtLeast_mono_restrict hr hsum)

