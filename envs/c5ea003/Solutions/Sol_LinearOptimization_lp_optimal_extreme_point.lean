-- Prove2me | solution 1 for LinearOptimization.lp_optimal_extreme_point
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T06:18:52.665413+00:00
-- url     : https://prove2.me/submissions/866f462b-37e5-4f67-bde9-2ca1896146bd

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_Polyhedron
import Theorems.Thm_LinearOptimization_lp_extreme_point_optimality

open Matrix LinearOptimization

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hext : (Set.extremePoints ℝ (polyhedron A b)).Nonempty)
    (hopt : ∃ x, IsLpOptimal c (polyhedron A b) x) :
    ∃ x ∈ Set.extremePoints ℝ (polyhedron A b),
      IsLpOptimal c (polyhedron A b) x := by
  rcases lp_extreme_point_optimality A b c hext with hbot | h
  · exfalso
    obtain ⟨x, hxmem, hxopt⟩ := hopt
    -- an optimal solution bounds the optimal cost from below, so it cannot be `⊥`
    have hge : ((c ⬝ᵥ x : ℝ) : EReal) ≤ lpValue c (polyhedron A b) := by
      rw [lpValue]
      refine le_iInf₂ ?_
      intro y hy
      exact_mod_cast hxopt y hy
    rw [hbot, le_bot_iff] at hge
    exact (EReal.coe_ne_bot _) hge
  · exact h
