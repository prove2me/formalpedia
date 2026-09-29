-- Prove2me | solution 1 for BanditAlgorithm.exists_action_outside_nonlocal_neighbourhood
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:13:13.02597+00:00
-- url     : https://prove2.me/submissions/7c8300f7-9b14-4b5f-bd33-11216c5ab9c2

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 37.12, Step 1,
printed p.488: failure of local observability supplies a neighbouring pair
which has no locally supported loss-difference estimator.  Global
observability then supplies a global estimator for that same pair; hence its
neighbourhood cannot contain every action.
-/

theorem exists_nonlocally_observable_neighbours
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (hloc : ¬ LocallyObservable G) :
    ∃ a b : Fin k, NeighbouringActions G a b ∧
      ¬ ∃ f : Fin k × 𝕊 → ℝ, IsLocalLossEstimator G a b f := by
  classical
  by_contra h
  apply hloc
  intro a b hab
  by_contra hnone
  exact h ⟨a, b, hab, hnone⟩

theorem exists_action_outside_nonlocal_neighbourhood
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (hglob : GloballyObservable G) (hloc : ¬ LocallyObservable G) :
    ∃ a b : Fin k, NeighbouringActions G a b ∧
      (∃ f : Fin k × 𝕊 → ℝ, IsGlobalLossEstimator G a b f) ∧
      ∃ c : Fin k, c ∉ pmNeighbourhood G a b := by
  classical
  obtain ⟨a, b, hab, hnlocal⟩ :=
    exists_nonlocally_observable_neighbours G hloc
  obtain ⟨f, hf⟩ := hglob a b hab
  refine ⟨a, b, hab, ⟨f, hf⟩, ?_⟩
  by_contra hout
  push_neg at hout
  apply hnlocal
  refine ⟨f, hf, ?_⟩
  intro c hc σ
  exact (hc (hout c)).elim

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (hglob : BanditAlgorithm.GloballyObservable G)
    (hloc : ¬ BanditAlgorithm.LocallyObservable G) :
    ∃ a b : Fin k, BanditAlgorithm.NeighbouringActions G a b ∧
      (∃ f : Fin k × 𝕊 → ℝ,
        BanditAlgorithm.IsGlobalLossEstimator G a b f) ∧
      ∃ c : Fin k, c ∉ BanditAlgorithm.pmNeighbourhood G a b :=
  BanditAlgorithm.exists_action_outside_nonlocal_neighbourhood G hglob hloc
