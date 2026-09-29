-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_easy_geometric_alternatives_of_outside
-- name    : BanditAlgorithm.partial_monitoring_easy_geometric_alternatives_of_outside
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:07:11.054334+00:00
-- url     : https://prove2.me/theorems/829abfe9-4d88-4109-bf96-4185a0936073
-- title:
--   Geometric alternatives around a neighbouring edge
-- statement:
--   Let $a,b$ be neighbouring actions and suppose their neighbourhood does not contain every action. Then there exist a positive interior distribution $u$, a zero-mass transverse direction $q$, and constants $\\varepsilon,\\delta>0$ such that every sufficiently small symmetric perturbation $u_a=u-\\Delta q$ and $u_b=u+\\Delta q$ remains in the cells of $a$ and $b$. Outside actions retain gap at least $\\varepsilon/2$, while each neighbourhood action's two endpoint-relative gaps sum exactly to $\\Delta$.\n\nThis is the finite-cell perturbation geometry used in the square-root lower bound.\n\n**Formalization Note** The transverse direction is obtained solely from neighbourhood geometry; no observability assumption is required.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 37.14 proof sketch, printed p. 492 (PDF p. 500), with the cell-stability and interpolation argument of Eqs. (37.5)–(37.10), printed pp. 488–491; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_transverse_direction
import Theorems.Thm_BanditAlgorithm_partial_monitoring_uniform_outside_gap
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_positive_common_point
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_loss_interpolation
import Theorems.Thm_stdSimplex_small_perturbation
import Theorems.Thm_finite_linear_gaps_stable
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

open Set

theorem BanditAlgorithm.partial_monitoring_easy_geometric_alternatives_of_outside
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b)
    (hout : ∃ c : Fin k, c ∉ pmNeighbourhood G a b) :
    ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ pmCell G a ∧ ub ∈ pmCell G b ∧
        (∀ c : Fin k, c ∉ pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ) := by
  sorry
