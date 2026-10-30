-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_forest_faces__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
-- name    : WilliamsonShmoys_planar_drawing_forest_faces__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:57:04.996984+00:00
-- url     : https://prove2.me/theorems/b41a74fa-21d0-4a74-8cba-62a4d9ab4259
-- title:
--   Face count from a spanning forest in a planar drawing
-- statement:
--   For the specified drawing and a spanning forest satisfying the stated acyclicity, reachability, and edge-count conditions, the number of complementary faces plus the forest edge count equals the full graph’s edge count plus one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_forest_faces__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
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
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (H : SimpleGraph V)
    (hsub : ∀ u v, H.Adj u v → G.Adj u v)
    (hacyclic : H.IsAcyclic)
    (hspan : ∀ u v, G.Reachable u v → H.Reachable u v)
    (hcard : H.edgeSet.ncard + Nat.card G.ConnectedComponent = Fintype.card V) :
    Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) + H.edgeSet.ncard =
      G.edgeSet.ncard + 1 := by sorry
