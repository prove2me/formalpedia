-- Prove2me | solution 1 for WorkbookRestored.plus_47859
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T12:08:42.068815+00:00
-- url     : https://prove2.me/submissions/aeae0262-e10b-47e9-9d66-45480fe853b3

/- Adapted from internlm/Lean-Workbook, Apache-2.0. Original row lean_workbook_plus_47859.
   Import/namespace repair; the mathematical statement is unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution (θ : ℝ) (h1 : 0 < θ) (h2 : θ < Real.pi / 2) : 2 > Real.tan θ * (1 - Real.sin θ)   := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h1 (by linarith [pi_pos])
  have hh : 1-sin θ ≤ cos θ := by
    nlinarith [sin_sq_add_cos_sq θ,mul_nonneg hs.le hc.le,sq_nonneg (sin θ+cos θ-1)]
  change tan θ * (1-sin θ) < 2
  rw [tan_eq_sin_div_cos,div_mul_eq_mul_div,div_lt_iff₀ hc]
  calc
    sin θ * (1-sin θ) ≤ sin θ*cos θ := mul_le_mul_of_nonneg_left hh hs.le
    _ ≤ cos θ := mul_le_of_le_one_left hc.le (sin_le_one θ)
    _ < 2*cos θ := by linarith
#print axioms solution
