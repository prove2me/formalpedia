-- Prove2me | Theorems.Thm_WilliamsonShmoys_straight_line_planar_edge_bound__p2m_31b80458_edea_4a06_ad98_a555b209930b_a3
-- name    : WilliamsonShmoys.straight_line_planar_edge_bound__p2m_31b80458_edea_4a06_ad98_a555b209930b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:44:48.180925+00:00
-- url     : https://prove2.me/theorems/3109c528-33f6-40b3-a5a4-3ed647da0089
-- title:
--   Euler edge bound for straight-line planar graphs
-- statement:
--   A simple graph on at least three vertices with a crossing-free straight-line drawing has at most `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.straight_line_planar_edge_bound__p2m_31b80458_edea_4a06_ad98_a555b209930b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : ∃ p : V → ℝ × ℝ, Function.Injective p ∧
      (∀ u v w, u < v → K.Adj u v → w ≠ u → w ≠ v →
        ∀ t ∈ Set.Ioo (0 : ℝ) 1,
          ((1 - t) • p u + t • p v) ≠ p w) ∧
      (∀ u v x y, u < v → x < y → K.Adj u v → K.Adj x y → (u, v) ≠ (x, y) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ((1 - t) • p u + t • p v) = ((1 - s) • p x + s • p y) →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
