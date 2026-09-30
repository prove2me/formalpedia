-- Prove2me | solution 1 for RybinAI2026.P01.psi_ge_inv_sqrt_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:56:38.885889+00:00
-- url     : https://prove2.me/submissions/31def561-20e3-491b-a015-a3edfb91747b

import Mathlib
import Theorems.Thm_RybinAI2026_P01_arctan_lower_slope

theorem solution (t : ℝ) (ht : 1 < t) :
    1 / Real.sqrt t ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
  let r := Real.sqrt (t - 1)
  have ht1 : 0 < t - 1 := sub_pos.mpr ht
  have hr : 0 < r := Real.sqrt_pos.2 ht1
  have hr2 : r ^ 2 = t - 1 := Real.sq_sqrt (le_of_lt ht1)
  have heval :
      (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) =
        r⁻¹ * Real.arctan r := by
    calc
      _ = ∫ s in (0 : ℝ)..1, (1 + (r * s) ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [← hr2]
        ring
      _ = r⁻¹ • ∫ u in r * 0..r * 1, (1 + u ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_comp_mul_left
          (f := fun u : ℝ => (1 + u ^ 2)⁻¹) hr.ne']
      _ = r⁻¹ * Real.arctan r := by simp
  have hroot : 0 < Real.sqrt (1 + r ^ 2) := by positivity
  have htan := RybinAI2026.P01.arctan_lower_slope r (le_of_lt hr)
  have hmul : r ≤ Real.arctan r * Real.sqrt (1 + r ^ 2) :=
    (div_le_iff₀ hroot).1 htan
  have hratio : 1 / Real.sqrt (1 + r ^ 2) ≤ Real.arctan r / r :=
    (div_le_div_iff₀ hroot hr).2 (by simpa using hmul)
  have htid : t = 1 + r ^ 2 := by nlinarith [hr2]
  have hsqrt : Real.sqrt t = Real.sqrt (1 + r ^ 2) := congrArg Real.sqrt htid
  calc
    1 / Real.sqrt t = 1 / Real.sqrt (1 + r ^ 2) := by rw [hsqrt]
    _ ≤ Real.arctan r / r := hratio
    _ = r⁻¹ * Real.arctan r := by ring
    _ = ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := heval.symm
