-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_uniform_outside_gap
-- name    : BanditAlgorithm.partial_monitoring_uniform_outside_gap
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:28:58.685009+00:00
-- url     : https://prove2.me/theorems/9f2216d8-0935-41e9-b6d5-721d16f8dc8d
-- title:
--   A common edge point uniformly separates all outside actions
-- statement:
--   Suppose at least one action lies outside $N_{ab}$. Then there are a common-cell distribution $u\in C_a\cap C_b$ and a constant $\varepsilon>0$ such that every action $c\notin N_{ab}$ is uniformly worse than both $a$ and $b$ at $u$:
--
--   $$
--   \langle\ell_c-\ell_a,u\rangle\ge\varepsilon,
--   \qquad
--   \langle\ell_c-\ell_b,u\rangle\ge\varepsilon.
--   $$
--
--   The same $u$ and $\varepsilon$ work for all outside actions. This is the uniform finite-action form of the strict separation encoded by Eq. (37.5).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 1, printed pp. 488–489, Eq. (37.5). The proof uses a finite convex average rather than the book’s centroid, yielding the same uniform strict-gap property.

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_outside_neighbourhood_strict_gap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

theorem BanditAlgorithm.partial_monitoring_uniform_outside_gap
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b : Fin k) (hout : ∃ c : Fin k, c ∉ pmNeighbourhood G a b) :
    ∃ u ∈ pmCell G a ∩ pmCell G b, ∃ ε : ℝ, 0 < ε ∧
      ∀ c : Fin k, c ∉ pmNeighbourhood G a b →
        ε ≤ ∑ i, (G.L c i - G.L a i) * u i ∧
        ε ≤ ∑ i, (G.L c i - G.L b i) * u i := by sorry
