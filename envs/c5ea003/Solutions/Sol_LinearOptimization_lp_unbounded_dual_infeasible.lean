-- Prove2me | solution 1 for LinearOptimization.lp_unbounded_dual_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:01:18.60259+00:00
-- url     : https://prove2.me/submissions/a689d0ef-de6c-40ab-9f59-2b255e0d4d87

import Definitions.Def_LinearOptimization_DualLP
import Theorems.Thm_LinearOptimization_lp_weak_duality

open Matrix LinearOptimization

theorem solution {m n : ℕ} (P : GeneralFormLP m n) :
    (lpValue P.c (generalFeasibleSet P) = ⊥ →
      generalFeasibleSet (dualLP P) = ∅) ∧
    (lpDualValue P.b (generalFeasibleSet (dualLP P)) = ⊤ →
      generalFeasibleSet P = ∅) := by
  constructor
  · intro hval
    by_contra hne
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
    -- Weak duality: every primal cost is at least `p ⬝ᵥ b`, so the primal infimum is too.
    have hbound : ((p ⬝ᵥ P.b : ℝ) : EReal) ≤ lpValue P.c (generalFeasibleSet P) := by
      unfold lpValue
      refine le_iInf₂ fun x hx => ?_
      exact_mod_cast LinearOptimization.lp_weak_duality P x hx p hp
    rw [hval] at hbound
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hbound)
  · intro hval
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    -- Weak duality: every dual objective is at most `c ⬝ᵥ x`, so the dual supremum is too.
    have hbound : lpDualValue P.b (generalFeasibleSet (dualLP P)) ≤ ((P.c ⬝ᵥ x : ℝ) : EReal) := by
      unfold lpDualValue
      refine iSup₂_le fun p hp => ?_
      exact_mod_cast LinearOptimization.lp_weak_duality P x hx p hp
    rw [hval] at hbound
    exact EReal.coe_ne_top _ (top_le_iff.mp hbound)
