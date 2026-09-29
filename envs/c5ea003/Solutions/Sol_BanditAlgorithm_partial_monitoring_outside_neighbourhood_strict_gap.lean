-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_outside_neighbourhood_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:24:50.583728+00:00
-- url     : https://prove2.me/submissions/b68699d0-1c1e-4eb0-9b14-25cd517df845

import Definitions.Def_PartialMonitoringGame
import Mathlib.Tactic

open Set

namespace BanditAlgorithm

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 37.12, Step 1,
printed pp.488--489, Eq. (37.5).  An action outside `N_ab` is strictly worse
than both incident actions somewhere on their common cell.
-/

theorem partial_monitoring_outside_neighbourhood_strict_gap
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b c : Fin k) (hc : c ∉ pmNeighbourhood G a b) :
    ∃ u ∈ pmCell G a ∩ pmCell G b,
      0 < ∑ i, (G.L c i - G.L a i) * u i ∧
      0 < ∑ i, (G.L c i - G.L b i) * u i := by
  classical
  obtain ⟨u, huab, huc⟩ := Set.not_subset.mp hc
  have hua : u ∈ pmCell G a := huab.1
  have hub : u ∈ pmCell G b := huab.2
  have hus : u ∈ stdSimplex ℝ (Fin d) := hua.1
  have huc' : ¬ ∀ e : Fin k,
      ∑ i, (G.L c i - G.L e i) * u i ≤ 0 := by
    intro h
    exact huc ⟨hus, h⟩
  push Not at huc'
  obtain ⟨e, he⟩ := huc'
  have hae := hua.2 e
  have hbe := hub.2 e
  refine ⟨u, huab, ?_, ?_⟩
  · have hid : (∑ i, (G.L c i - G.L a i) * u i) =
        (∑ i, (G.L c i - G.L e i) * u i) -
          ∑ i, (G.L a i - G.L e i) * u i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hid]
    linarith
  · have hid : (∑ i, (G.L c i - G.L b i) * u i) =
        (∑ i, (G.L c i - G.L e i) * u i) -
          ∑ i, (G.L b i - G.L e i) * u i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hid]
    linarith

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (a b c : Fin k)
    (hc : c ∉ BanditAlgorithm.pmNeighbourhood G a b) :
    ∃ u ∈ BanditAlgorithm.pmCell G a ∩ BanditAlgorithm.pmCell G b,
      0 < ∑ i, (G.L c i - G.L a i) * u i ∧
      0 < ∑ i, (G.L c i - G.L b i) * u i :=
  BanditAlgorithm.partial_monitoring_outside_neighbourhood_strict_gap G a b c hc
