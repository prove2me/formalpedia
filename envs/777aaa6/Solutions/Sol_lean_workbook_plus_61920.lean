-- Prove2me | solution 1 for lean_workbook_plus_61920
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:59.343109+00:00
-- url     : https://prove2.me/submissions/bcaf5896-8393-432f-9c21-6e2e093e37e2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 5000
theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) + f (x - y) - 2 * f x * f (1 + y) = 2 * x * y * (3 * y - x ^ 2)) : ∃ c, ∀ x, f x = c * x ^ 3   :=  by
  have h0 := hf 1 0
  have hp := hf 1 1
  have hn := hf 1 (-1)
  norm_num at h0 hp hn
  have hm : f 1 * (f 1-1) = 0 := by
    calc
      _ = -(f 1 + f 1 - 2 * f 1 * f 1)/2 := by ring
      _ = 0 := by rw [h0]; norm_num
  rcases mul_eq_zero.mp hm with hz | ho
  · simp [hz] at hp hn
    have he : (4:ℝ) = 8 := calc
      4 = f 2 + f 0 := hp.symm
      _ = f 0 + f 2 := add_comm _ _
      _ = 8 := hn
    norm_num at he
  · have hz : f 1=1 := sub_eq_zero.mp ho
    simp [hz] at hp hn
    have he : (4:ℝ)+8 = 0 := calc
      _ = (f 2+f 0-2*f 2)+(f 0+f 2-2*f 0) := by rw [hp, hn]
      _ = 0 := by ring
    norm_num at he
#print axioms solution
