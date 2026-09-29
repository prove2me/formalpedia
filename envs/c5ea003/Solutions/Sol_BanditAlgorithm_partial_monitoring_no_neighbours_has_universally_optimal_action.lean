-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_no_neighbours_has_universally_optimal_action
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T18:50:34.437054+00:00
-- url     : https://prove2.me/submissions/87fa9c7f-0b19-431a-b145-06534523fb06

import Theorems.Thm_BanditAlgorithm_partial_monitoring_pareto_monotone_neighbour_paths

open MeasureTheory ProbabilityTheory

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (hk : 0 < k) (hd : 0 < d)
    (h : ¬ BanditAlgorithm.HasNeighbouringActions G) :
    ∃ a : Fin k, ∀ b : Fin k, ∀ i : Fin d, G.L a i ≤ G.L b i := by
  classical
  by_cases hk1 : k = 1
  · subst k
    refine ⟨0, ?_⟩
    intro b i
    simpa [Subsingleton.elim b 0]
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨S, hSne, hbest, hpaths⟩ :=
      BanditAlgorithm.partial_monitoring_pareto_monotone_neighbour_paths G hk2 hd
    let lam : Fin d → ℝ := fun _ ↦ 1 / d
    have hlam : lam ∈ stdSimplex ℝ (Fin d) := by
      constructor
      · intro i
        dsimp [lam]
        positivity
      · simp [lam, hd.ne']
    obtain ⟨root, hrootS, hrootPath⟩ := hpaths lam hlam
    have hSroot : ∀ b ∈ S, b = root := by
      intro b hbS
      obtain ⟨m, path, hmle, hfirst, hlast, hpathS, hedges⟩ := hrootPath b hbS
      by_cases hm : m = 0
      · subst m
        simpa using hfirst.symm.trans hlast
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        let t : Fin m := ⟨0, hmpos⟩
        exact False.elim (h ⟨path t.castSucc, path t.succ, (hedges t).1⟩)
    refine ⟨root, ?_⟩
    intro b i
    let out : Fin 1 → Fin d := fun _ ↦ i
    obtain ⟨a, haS, habest⟩ := hbest 1 out
    have haroot : a = root := hSroot a haS
    have hab := habest b
    simpa [out, haroot] using hab
