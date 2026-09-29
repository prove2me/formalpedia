-- Prove2me | solution 1 for Bishop.Reg.lt_iff_toReal_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:58:01.155163+00:00
-- url     : https://prove2.me/submissions/a5eb982a-a289-4c19-8e0f-8689b9cda187

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
open Bishop Bishop.Reg Filter Topology in
theorem solution (x y : Reg) : Lt x y ↔ x.toReal < y.toReal := by
  constructor
  · -- a gap of `2/(n+1)` at stage `n` survives the two moduli of `1/(n+1)` each
    rintro ⟨n, hn⟩
    have hnr : ((x.approx n : ℚ) : ℝ) + 2 / ((n : ℝ) + 1) < ((y.approx n : ℚ) : ℝ) := by
      have h : ((x.approx n + 2 / (n + 1 : ℚ) : ℚ) : ℝ) < ((y.approx n : ℚ) : ℝ) := by
        exact_mod_cast hn
      push_cast at h
      exact h
    have hx := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le x n)
    have hy := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le y n)
    have hsplit : (2 : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    linarith [hx.1, hx.2, hy.1, hy.2]
  · -- conversely take `n` with `4/(n+1) < y - x`, leaving `2/(n+1)` after both moduli
    intro hlt
    have hd : 0 < y.toReal - x.toReal := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (4 / (y.toReal - x.toReal))
    show ∃ n : ℕ, x.approx n + 2 / (n + 1 : ℚ) < y.approx n
    refine ⟨n, ?_⟩
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlt4 : 4 / ((n : ℝ) + 1) < y.toReal - x.toReal := by
      rw [div_lt_iff₀ hn1]
      rw [div_lt_iff₀ hd] at hn
      nlinarith [hn, hd]
    have hx := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le x n)
    have hy := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le y n)
    have hsplit : (4 : ℝ) / ((n : ℝ) + 1)
        = 2 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    have hreal : ((x.approx n : ℚ) : ℝ) + 2 / ((n : ℝ) + 1) < ((y.approx n : ℚ) : ℝ) := by
      linarith [hx.1, hx.2, hy.1, hy.2]
    have hcast : ((x.approx n + 2 / (n + 1 : ℚ) : ℚ) : ℝ) < ((y.approx n : ℚ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast hcast
