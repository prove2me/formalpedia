-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_pareto_cover_ranked_descent
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T19:10:12.188781+00:00
-- url     : https://prove2.me/submissions/3fe2097d-5ff3-4091-af65-1adfee382dc3

import Theorems.Thm_BanditAlgorithm_partial_monitoring_unique_pareto_cell_cover_best
import Theorems.Thm_BanditAlgorithm_partial_monitoring_duplicate_free_pareto_cell_cover_ranked_descent

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d) :
    ∃ S : Finset (Fin k),
      S.Nonempty ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
        ∃ root ∈ S, ∃ rank : Fin k → ℕ,
          ∀ b ∈ S, b ≠ root →
            ∃ c ∈ S, NeighbouringActions G b c ∧
              ∑ i : Fin d, G.L c i * lam i ≤
                ∑ i : Fin d, G.L b i * lam i ∧
              rank c < rank b := by
  obtain ⟨S, hSne, hpareto, hunique, hcover, hbest⟩ :=
    partial_monitoring_unique_pareto_cell_cover_best G (by omega) hd
  exact ⟨S, hSne, hbest,
    partial_monitoring_duplicate_free_pareto_cell_cover_ranked_descent
      G hd S hSne hpareto hunique hcover⟩

end BanditAlgorithm
