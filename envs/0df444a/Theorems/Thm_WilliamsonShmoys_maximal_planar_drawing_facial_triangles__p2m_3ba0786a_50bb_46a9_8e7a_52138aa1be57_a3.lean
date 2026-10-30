-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_facial_triangles__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_facial_triangles__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:53:32.948609+00:00
-- url     : https://prove2.me/theorems/69f7c61b-c390-4365-9e4f-b0c1ff980885
-- title:
--   Facial triangular data for a maximal planar drawing
-- statement:
--   A maximal drawable graph with at least three vertices admits finite triangular face data whose sides biject with its oriented edges. The dart endpoints match consecutive corners, each triangle has distinct corners, and every vertex appears.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_facial_triangles__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F)
      (corner : F → Fin 3 → V)
      (dart : (F × Fin 3) ≃ H.Dart),
      (∀ f i, (dart (f, i)).fst = corner f i) ∧
      (∀ f i, (dart (f, i)).snd = corner f (i + 1)) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) := by sorry
