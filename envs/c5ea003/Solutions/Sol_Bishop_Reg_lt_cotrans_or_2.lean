-- Prove2me | solution 2 for Bishop.Reg.lt_cotrans_or
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:53:35.887582+00:00
-- url     : https://prove2.me/submissions/d87afb02-7a7b-4a5c-884f-fd01cef465fe

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
open Bishop Bishop.Reg Filter Topology in
theorem solution {x y : Reg} (h : Lt x y) (z : Reg) : Lt x z ∨ Lt z y := by
  -- the order on Bishop reals is exactly the order on the reals they denote
  have hiff : ∀ a b : Reg, Lt a b ↔ a.toReal < b.toReal := by
    intro a b
    constructor
    · -- a gap of `2/(n+1)` at stage `n` survives the two moduli of `1/(n+1)` each
      rintro ⟨n, hn⟩
      have hnr : ((a.approx n : ℚ) : ℝ) + 2 / ((n : ℝ) + 1) < ((b.approx n : ℚ) : ℝ) := by
        have h : ((a.approx n + 2 / (n + 1 : ℚ) : ℚ) : ℝ) < ((b.approx n : ℚ) : ℝ) := by
          exact_mod_cast hn
        push_cast at h
        exact h
      have hx := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le a n)
      have hy := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le b n)
      have hsplit : (2 : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
      linarith [hx.1, hx.2, hy.1, hy.2]
    · -- conversely take `n` with `4/(n+1) < b - a`, leaving `2/(n+1)` after both moduli
      intro hlt
      have hd : 0 < b.toReal - a.toReal := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (4 / (b.toReal - a.toReal))
      show ∃ n : ℕ, a.approx n + 2 / (n + 1 : ℚ) < b.approx n
      refine ⟨n, ?_⟩
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hlt4 : 4 / ((n : ℝ) + 1) < b.toReal - a.toReal := by
        rw [div_lt_iff₀ hn1]
        rw [div_lt_iff₀ hd] at hn
        nlinarith [hn, hd]
      have hx := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le a n)
      have hy := abs_le.mp (Bishop.Reg.abs_toReal_sub_approx_le b n)
      have hsplit : (4 : ℝ) / ((n : ℝ) + 1)
          = 2 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
      have hreal : ((a.approx n : ℚ) : ℝ) + 2 / ((n : ℝ) + 1) < ((b.approx n : ℚ) : ℝ) := by
        linarith [hx.1, hx.2, hy.1, hy.2]
      have hcast : ((a.approx n + 2 / (n + 1 : ℚ) : ℚ) : ℝ) < ((b.approx n : ℚ) : ℝ) := by
        push_cast
        exact hreal
      exact_mod_cast hcast
  -- cotransitivity is then trichotomy on `ℝ`
  have hxy : x.toReal < y.toReal := (hiff x y).mp h
  rcases lt_or_ge x.toReal z.toReal with hz | hz
  · exact Or.inl ((hiff x z).mpr hz)
  · exact Or.inr ((hiff z y).mpr (lt_of_le_of_lt hz hxy))
