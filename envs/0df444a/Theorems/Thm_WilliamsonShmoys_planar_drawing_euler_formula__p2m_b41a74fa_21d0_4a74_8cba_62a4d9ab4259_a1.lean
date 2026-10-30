-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula__p2m_b41a74fa_21d0_4a74_8cba_62a4d9ab4259_a1
-- name    : WilliamsonShmoys_planar_drawing_euler_formula__p2m_b41a74fa_21d0_4a74_8cba_62a4d9ab4259_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:07.230332+00:00
-- url     : https://prove2.me/theorems/7ba2c610-fb3f-48a8-aaca-ee4efbd0ab70
-- title:
--   Euler formula for the specified planar drawing
-- statement:
--   For a finite graph with an injective vertex placement and continuous, simple, pairwise noncrossing edge arcs that avoid vertices in their interiors, the number of connected components of the drawing's complement plus the number of vertices equals the number of edges plus the number of graph components plus one. The formula includes disconnected graphs and isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_euler_formula__p2m_b41a74fa_21d0_4a74_8cba_62a4d9ab4259_a1
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
    Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) +
        Fintype.card V =
      G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by sorry
