-- Prove2me | solution 1 for BanditAlgorithm.mdp_regret_lower_bound_large_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-04T23:12:23.158589+00:00
-- url     : https://prove2.me/submissions/b6d148f9-2b0e-4c26-8c9c-940c70497cf5

import Theorems.Thm_BanditAlgorithm_arena_family_exists_uniform
import Theorems.Thm_BanditAlgorithm_arena_family_step_two
import Theorems.Thm_BanditAlgorithm_arena_lower_bound_parameter_choice
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open BanditAlgorithm BanditAlgorithm.LayeredArena

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, ∀ D : ℝ, 3 ≤ S → 2 ≤ A →
        20 * (1 + Real.log S / Real.log A) ≤ D → D * S * A ≤ n →
        ∀ π : MDPPolicy S A,
          ∃ M : FiniteMDP S A, ∃ μ0 : MDPStateDistribution S,
            mdpDiameterENN M ≤ ENNReal.ofReal D ∧
            C * Real.sqrt (D * S * A * n) ≤
              ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) := by
  refine ⟨1 / 12500, by norm_num, ?_⟩
  intro S A n D hS hA hD hn π
  haveI : NeZero S := ⟨by omega⟩
  -- the hard family, its skeleton data and its uniform diameter bound
  obtain ⟨E₀, Efam, L, hg, hb, hr, hl, hdp, hc, hsl, hsa, hcard, hL1, hdep, hLb, hdiam⟩ :=
    BanditAlgorithm.arena_family_exists_uniform (S := S) (A := A) hS hA
  -- the tuning: every constraint of Step 2 is satisfiable with room for the rate
  obtain ⟨δ, Δ, N, ε, c₁, c₂, c₃, Dsc, hδ1, hδ0, hΔ4, hΔ2, hk2, hn0, hN0, hDsc0,
      hc₁, hc₂, hc₃, hcap, hc₃D, hlo, hhi, ht1, ht2, hΔt, hdiamD, hrate⟩ :=
    BanditAlgorithm.arena_lower_bound_parameter_choice S A n L E₀.depth
      (Fintype.card ↥(countedPairs (A := A) E₀.leafNat)) D hS hA hD hn hdep hLb hL1 hcard
  -- Step 2: some member of the family forces the learner into large regret
  obtain ⟨p, hp⟩ :=
    BanditAlgorithm.arena_family_step_two hδ1 hδ0 hΔ4 hΔ2 E₀ Efam hg hb hr hl hdp hc hsl hsa
      (by omega) (by omega) π n N _ Dsc c₁ c₂ c₃ rfl hk2 hn0 hN0 hDsc0 hc₁ hc₂ hc₃
      hcap hc₃D ε hlo hhi ht1 ht2 hΔt
  refine ⟨(Efam p).toMDP hδ1 hΔ2, mdpStateDirac (Efam p).root, ?_, le_trans hrate hp⟩
  exact le_trans (hdiam δ Δ hδ1 hΔ2 hδ0 hΔ4 p) (ENNReal.ofReal_le_ofReal hdiamD)
