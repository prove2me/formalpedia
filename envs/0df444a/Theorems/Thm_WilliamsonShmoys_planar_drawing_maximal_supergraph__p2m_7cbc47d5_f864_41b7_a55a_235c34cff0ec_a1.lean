-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:47.783817+00:00
-- url     : https://prove2.me/theorems/30147cc2-3609-4f7e-9a97-a6f7a798fcab
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. Its edge count is at least the original graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_7cbc47d5_f864_41b7_a55a_235c34cff0ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) := by sorry
