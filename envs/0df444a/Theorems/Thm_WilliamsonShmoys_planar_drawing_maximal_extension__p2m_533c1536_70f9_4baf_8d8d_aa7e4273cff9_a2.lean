-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:40.47445+00:00
-- url     : https://prove2.me/theorems/62578b33-7986-4643-ae9c-c0cb30164949
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on the given finite vertex set has a drawable supergraph with at least as many edges that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_533c1536_70f9_4baf_8d8d_aa7e4273cff9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry
