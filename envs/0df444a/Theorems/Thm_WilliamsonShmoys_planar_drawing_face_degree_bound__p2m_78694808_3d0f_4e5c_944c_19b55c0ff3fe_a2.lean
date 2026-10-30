-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_degree_bound__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
-- name    : WilliamsonShmoys.planar_drawing_face_degree_bound__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:38:28.134972+00:00
-- url     : https://prove2.me/theorems/fab32fe7-d04d-40fd-bd1f-2979d59b61b6
-- title:
--   Lower bound on total facial degree
-- statement:
--   For a finite graph drawing satisfying the target's geometric hypotheses and having at least two edges, three times the number of complementary faces is at most twice the number of edges. The argument must account for bridges and disconnected components using the total face-boundary incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_degree_bound__p2m_78694808_3d0f_4e5c_944c_19b55c0ff3fe_a2
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
    (hE : 2 ≤ G.edgeSet.ncard) :
    3 * Nat.card (WilliamsonShmoys_PlanarDrawingFaces__p2m_1080ccf9_69ad_46ce_852f_7faab6d5860a_a9 G p arc) ≤
      2 * G.edgeSet.ncard := by sorry
