-- Prove2me | solution 3 for BanditAlgorithm.mdp_regret_lower_bound_jao_universal_constant_large_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-06T14:04:58.378573+00:00
-- url     : https://prove2.me/submissions/764cfbc0-0da4-454f-98c0-397ecbb2852d

import Theorems.Thm_BanditAlgorithm_mdp_regret_lower_bound_jao_large_diameter

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

/-!
# `mdp_regret_lower_bound_jao_universal_constant_large_diameter`

Target: `BanditAlgorithm.mdp_regret_lower_bound_jao_universal_constant_large_diameter`
(`7dcd3175-7a42-4385-8b94-33e96fae3312`, Open).

The target asks only for the EXISTENCE of a positive constant `C` for which the
Jaksch–Ortner–Auer large-diameter lower bound holds.  The platform theorem
`BanditAlgorithm.mdp_regret_lower_bound_jao_large_diameter`
(`152e5cf3-0902-4395-82ad-f1aa4a56d6aa`, **Proved**) is the same statement with the
explicit constant `0.015`, under exactly the same hypotheses
(`10 ≤ S`, `10 ≤ A`, `20 log_A S ≤ D`, `D·S·A ≤ T`, `12 ≤ D`) and with the same
conclusion (an MDP of diameter at most `D` whose expected regret from EVERY initial
state is at least `C √(D S A T)`).

So the existential is witnessed by `C = 0.015`, which is positive.  This is a
reduction whose single imported child is already `Proved`, hence a complete proof
with no open dependency.
-/

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
        20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
          ∀ π : MDPPolicy S A,
            ∃ M : FiniteMDP S A,
              mdpDiameterENN M ≤ ENNReal.ofReal D ∧
              ∀ s : Fin S,
                C * Real.sqrt (D * S * A * T) ≤
                  ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) :=
  ⟨0.015, by norm_num, BanditAlgorithm.mdp_regret_lower_bound_jao_large_diameter⟩
