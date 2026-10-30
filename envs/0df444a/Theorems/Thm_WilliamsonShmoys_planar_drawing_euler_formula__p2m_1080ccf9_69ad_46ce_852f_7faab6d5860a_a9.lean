-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
-- name    : WilliamsonShmoys.planar_drawing_euler_formula__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:03:05.063519+00:00
-- url     : https://prove2.me/theorems/e9afcc95-ed4a-4c92-9086-c25618dbb046
-- title:
--   Finite faces and Euler formula for a noncrossing arc drawing
-- statement:
--   For any specified drawing satisfying exactly the injectivity, arc, and nonintersection conditions of HasPlanarDrawingOn, the complement has finitely many connected components, and vertices plus faces equals edges plus graph components plus one. This includes disconnected graphs, isolated vertices, and the empty graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.planar_drawing_euler_formula__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc u v t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    Finite (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) ∧
      Fintype.card V + Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) =
        G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  sorry
