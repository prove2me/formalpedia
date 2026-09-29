-- Prove2me | solution 1 for Probability.PortfolioRegret.irred_dialValue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:28:48.499716+00:00
-- url     : https://prove2.me/submissions/ad5fe012-a08d-43b2-801b-ffcd0b13f747

import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioIrredundant
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore
open Probability.PortfolioRegret in
theorem solution {e : ℚ} (he : 0 < e) : dialValue irredW (irredCost e) id = 0 := by
  unfold dialValue
  apply Finset.sum_eq_zero
  intro o _
  apply le_antisymm
  · -- on its own fibre, the matching member `s = o` costs nothing
    calc _ ≤ fiberVal irredW (irredCost e) id o o := Finset.inf'_le _ (Finset.mem_univ o)
      _ = 0 := by
        unfold fiberVal
        apply Finset.sum_eq_zero
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hω
        subst hω
        simp only [irredCost]
        fin_cases ω <;> simp
  · -- and every cost is nonnegative
    apply Finset.le_inf'
    intro s _
    unfold fiberVal
    apply Finset.sum_nonneg
    intro ω _
    apply mul_nonneg (by simp [irredW])
    simp only [irredCost]
    split_ifs <;> linarith
