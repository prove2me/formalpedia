-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_locally_observable_upper_bound_discrete_signals
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:50:16.787671+00:00
-- url     : https://prove2.me/submissions/257d2067-ed76-4d01-8845-3d6f45d97f00

import Theorems.Thm_BanditAlgorithm_partial_monitoring_algorithm26_master_bound
import Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_algorithm26_solver
import Theorems.Thm_BanditAlgorithm_pmMinimaxRegret_le_policy_of_unit_losses

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

noncomputable section

private noncomputable def pmFixedPolicy
    {k : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊] (a : Fin k) : PMPolicy k 𝕊 where
  select := fun _ => Kernel.const _ (Measure.dirac a)
  markov := fun _ => inferInstance

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      pmMinimaxRegret G n ≤
        C * max 1 (pmLocObsConst G) * (k : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt (n * Real.log k) := by
  classical
  have hk0 : 0 < k := by omega
  let a0 : Fin k := ⟨0, hk0⟩
  by_cases hd : 0 < d
  · obtain ⟨S, C, hS, hC, hbest, hsolver⟩ :=
      partial_monitoring_locally_observable_algorithm26_solver G hk hd hL hloc
    refine ⟨C, hC, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simp [pmMinimaxRegret, pmRegret, pmMeasure]
    · obtain ⟨η, B, hη, hB, hscalar, hsolve⟩ := hsolver n (Nat.pos_of_ne_zero hn)
      obtain ⟨π, hπ⟩ := partial_monitoring_algorithm26_master_bound
        G S hS η B hη hd hbest hsolve n
      exact (pmMinimaxRegret_le_policy_of_unit_losses G (by omega) hL π).trans
        (hπ.trans hscalar)
  · have hd0 : d = 0 := by omega
    subst d
    refine ⟨1, by norm_num, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simp [pmMinimaxRegret, pmRegret, pmMeasure]
    · have hempty : IsEmpty (Fin n → Fin 0) := by
        constructor
        intro f
        exact Fin.elim0 (f ⟨0, Nat.pos_of_ne_zero hn⟩)
      letI : IsEmpty (Fin n → Fin 0) := hempty
      simp [pmMinimaxRegret]
      positivity

end
end BanditAlgorithm
