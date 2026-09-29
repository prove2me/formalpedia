-- Prove2me | solution 1 for BanditAlgorithm.mdp_confidence_union_bound_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T21:17:05.863563+00:00
-- url     : https://prove2.me/submissions/3418ec83-52ca-4515-9618-0244ee810c8b

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped NNReal ENNReal

/-!
The union bound of UCRL2 closes at `δ/2`.

Writing `Y = 2 S A n / δ ≥ 4`, the left-hand side is `S A n · 2^S · Y^{-7S}`.
The count `S A n` is `Y δ / 2`, and `2^S ≤ Y^{S/2}` because `Y ≥ 4`, so the whole
expression is `(δ/2) · Y^{1 - 13S/2}`; for `S ≥ 2` that exponent is at most `-12`,
and `Y ≥ 1`, so the remaining power is at most one.
-/

theorem solution
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    (S : ℝ) * A * n *
        (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ))))
      ≤ δ / 2 := by
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hSR : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : (4 : ℝ) ≤ 2 * S * A * n := by
    have e1 : (4 : ℝ) * 1 ≤ 2 * (S : ℝ) * A :=
      mul_le_mul (by linarith) hAR (by norm_num) (by linarith)
    have e2 : (4 : ℝ) * 1 ≤ 2 * (S : ℝ) * A * n :=
      mul_le_mul (by linarith) hnR (by norm_num) (by linarith)
    linarith
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 2 * S * A * n / δ := ⟨_, rfl⟩
  have hY4 : (4 : ℝ) ≤ Y := by rw [hYdef, le_div_iff₀ hδ0]; nlinarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hSAn : (S : ℝ) * A * n = Y * δ / 2 := by
    rw [hYdef]; field_simp
  rw [← hYdef, hSAn]
  -- the exponential is a power of `Y`
  have hexp : Real.exp (-(7 * (S : ℝ) * Real.log Y)) = Y ^ (-(7 * (S : ℝ))) := by
    rw [Real.rpow_def_of_pos hY0]; ring_nf
  rw [hexp]
  -- `2 ^ S ≤ Y ^ (S / 2)` because `Y ≥ 4`
  have h41 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have heq : (4 : ℝ) ^ ((S : ℝ) / 2) = 2 ^ S := by
    rw [show ((S : ℝ) / 2) = (1 / 2 : ℝ) * S by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4), h41, Real.rpow_natCast]
  have h2S : (2 : ℝ) ^ S ≤ Y ^ ((S : ℝ) / 2) := by
    have h4 : (4 : ℝ) ^ ((S : ℝ) / 2) ≤ Y ^ ((S : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) hY4 (by positivity)
    linarith [heq ▸ h4]
  have hstep : Y * δ / 2 * (2 ^ S * Y ^ (-(7 * (S : ℝ))))
      ≤ Y * δ / 2 * (Y ^ ((S : ℝ) / 2) * Y ^ (-(7 * (S : ℝ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right h2S (Real.rpow_nonneg hY0.le _)
  refine hstep.trans ?_
  have hfold : Y * δ / 2 * (Y ^ ((S : ℝ) / 2) * Y ^ (-(7 * (S : ℝ))))
      = δ / 2 * Y ^ (1 + ((S : ℝ) / 2 + -(7 * (S : ℝ)))) := by
    rw [Real.rpow_add hY0, Real.rpow_add hY0, Real.rpow_one]; ring
  rw [hfold]
  have hle1 : Y ^ (1 + ((S : ℝ) / 2 + -(7 * (S : ℝ)))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  nlinarith [hle1, hδ0.le, Real.rpow_nonneg hY0.le (1 + ((S : ℝ) / 2 + -(7 * (S : ℝ))))]
