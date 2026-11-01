-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_straight_line_triangulation__p2m_9b625ce0_21a3_499d_bb1b_40258fa2706e_a2
-- name    : WilliamsonShmoys.exists_straight_line_triangulation__p2m_9b625ce0_21a3_499d_bb1b_40258fa2706e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:01.20426+00:00
-- url     : https://prove2.me/theorems/f098d7ef-84ef-48f9-82ee-bb0f858b20b9
-- title:
--   Straight-line triangulation with the planar edge bound
-- statement:
--   For each finite linearly ordered vertex type with at least three elements, construct a graph with a crossing-free straight-line drawing and exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_straight_line_triangulation__p2m_9b625ce0_21a3_499d_bb1b_40258fa2706e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj)
      (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ u v, u < v → L.Adj u v →
        ContinuousOn (arc u v) (Set.Icc 0 1) ∧
        Set.InjOn (arc u v) (Set.Icc 0 1) ∧
        arc u v 0 = p u ∧
        arc u v 1 = p v ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w) ∧
      (∀ u v x y, u < v → x < y → L.Adj u v → L.Adj x y →
        (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
          arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      (∀ u v t, arc u v t = (1 - t) • p u + t • p v) ∧
      L.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
