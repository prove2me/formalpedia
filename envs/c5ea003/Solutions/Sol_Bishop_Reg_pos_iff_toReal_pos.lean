-- Prove2me | solution 1 for Bishop.Reg.pos_iff_toReal_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:49:14.728045+00:00
-- url     : https://prove2.me/submissions/8725b3bd-9cb2-4453-9f01-856eca99f507

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
open Bishop Bishop.Reg Filter Topology in
theorem solution (x : Reg) : Pos x ↔ 0 < x.toReal := by
  constructor
  · -- a rational witness `1/(n+1) < x_n` beats the modulus `|x - x_n| ≤ 1/(n+1)`
    rintro ⟨n, hn⟩
    have hmod := Bishop.Reg.abs_toReal_sub_approx_le x n
    have hnr : (1 : ℝ) / ((n : ℝ) + 1) < ((x.approx n : ℚ) : ℝ) := by
      have h : ((1 / (n + 1 : ℚ) : ℚ) : ℝ) < ((x.approx n : ℚ) : ℝ) := by exact_mod_cast hn
      push_cast at h
      exact h
    have h1 : ((x.approx n : ℚ) : ℝ) - x.toReal ≤ 1 / ((n : ℝ) + 1) := by
      have h := abs_le.mp hmod
      linarith [h.1, h.2]
    linarith
  · -- conversely pick `n` with `2/(n+1) < x`, so the modulus leaves room
    intro hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / x.toReal)
    show ∃ n : ℕ, 1 / (n + 1 : ℚ) < x.approx n
    refine ⟨n, ?_⟩
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlt : 2 / ((n : ℝ) + 1) < x.toReal := by
      rw [div_lt_iff₀ hn1]
      rw [div_lt_iff₀ hpos] at hn
      nlinarith [hn, hpos]
    have hmod := Bishop.Reg.abs_toReal_sub_approx_le x n
    have h2 : x.toReal - ((x.approx n : ℚ) : ℝ) ≤ 1 / ((n : ℝ) + 1) := (abs_le.mp hmod).2
    have hsplit : (2 : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    have hreal : (1 : ℝ) / ((n : ℝ) + 1) < ((x.approx n : ℚ) : ℝ) := by linarith
    have hcast : ((1 / (n + 1 : ℚ) : ℚ) : ℝ) < ((x.approx n : ℚ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast hcast
