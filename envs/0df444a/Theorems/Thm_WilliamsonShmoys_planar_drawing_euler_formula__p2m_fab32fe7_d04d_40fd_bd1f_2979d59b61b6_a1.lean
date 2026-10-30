-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_formula__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:43:07.681845+00:00
-- url     : https://prove2.me/theorems/1ef7e65a-ff27-4a11-b32b-f50205c0891f
-- title:
--   Euler formula for drawing complement components
-- statement:
--   For a finite graph drawing satisfying the target’s geometric hypotheses, the number of complementary faces plus the number of vertices equals the number of edges plus the number of graph connected components plus one. This formulation includes isolated vertices and disconnected drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_formula__p2m_fab32fe7_d04d_40fd_bd1f_2979d59b61b6_a1
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
    Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) + Fintype.card V =
      G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by sorry
