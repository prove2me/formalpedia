-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_with_two_roots_on_common_exterior_line__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
-- name    : WilliamsonShmoys.planar_drawing_with_two_roots_on_common_exterior_line__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:12.251067+00:00
-- url     : https://prove2.me/theorems/68a0df03-3b0e-4c4b-8e88-ddcf23a5e0ad
-- title:
--   Normalize a planar drawing above a line through two separated vertices
-- statement:
--   Redraw the graph so the two vertices in different components are ordered points on the horizontal axis, all other vertices are above that axis, and every edge interior lies strictly above it, while preserving the planar drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_with_two_roots_on_common_exterior_line__p2m_3e6d8a60_d3d3_4ec8_8c95_56c4b76ce917_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hnot : ¬ G.Reachable u v) :
    ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
      (Function.Injective p ∧
        (∀ a b, a < b → G.Adj a b →
          ContinuousOn (arc a b) (Set.Icc 0 1) ∧
          Set.InjOn (arc a b) (Set.Icc 0 1) ∧
          arc a b 0 = p a ∧ arc a b 1 = p b ∧
          ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
        (∀ a b c d, a < b → c < d → G.Adj a b → G.Adj c d →
          (a, b) ≠ (c, d) →
          ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            arc a b t = arc c d s →
              (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))) ∧
      (p u).2 = 0 ∧ (p v).2 = 0 ∧ (p u).1 < (p v).1 ∧
      (∀ w, w ≠ u → w ≠ v → 0 < (p w).2) ∧
      (∀ a b, a < b → G.Adj a b →
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (arc a b t).2) := by sorry
