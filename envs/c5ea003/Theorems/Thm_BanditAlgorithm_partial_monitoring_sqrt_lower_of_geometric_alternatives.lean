-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_sqrt_lower_of_geometric_alternatives
-- name    : BanditAlgorithm.partial_monitoring_sqrt_lower_of_geometric_alternatives
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:59:54.776124+00:00
-- url     : https://prove2.me/theorems/b3d3c260-4eda-49bb-bfcf-9b5d7fd0e56a
-- title:
--   Geometric alternatives imply a square-root partial-monitoring lower bound
-- statement:
--   Suppose a finite partial-monitoring game has a neighbouring pair admitting symmetric outcome perturbations of size $\Delta$: each perturbation stays in the corresponding endpoint cell, outside-neighbourhood actions retain a uniform positive gap, and the two endpoint-relative gaps of every neighbourhood action sum to $\Delta$. Then there are constants $c>0$ and $N$ such that for all $n\ge N$,
--
--   $$
--   R_n^*(G)\ge c\sqrt n.
--   $$
--
--   The proof bounds every one-step signal KL divergence by $O(\Delta^2)$, hence the full-history KL by $O(n\Delta^2)$, and chooses $\Delta$ proportional to $n^{-1/2}$ in the two-environment testing inequality.
--
--   **Formalization Note** The conclusion is independent of observability; observability is used elsewhere only to classify which upper bound also holds.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 37.14 proof sketch, printed p. 492 (PDF p. 500), using the testing argument of Theorem 37.12, Eqs. (37.8)–(37.10); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.partial_monitoring_sqrt_lower_of_geometric_alternatives
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (hgeom : ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
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
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * Real.sqrt n ≤ pmMinimaxRegret G n := by
  sorry
