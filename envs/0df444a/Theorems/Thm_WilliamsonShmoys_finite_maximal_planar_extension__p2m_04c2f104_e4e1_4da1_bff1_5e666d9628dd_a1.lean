-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_extension__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:16:58.7441+00:00
-- url     : https://prove2.me/theorems/526cd27f-7fba-4d69-b914-bdd8e77e9316
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type whose edge set is inclusion-maximal among drawable supergraphs. This isolates the finite selection step from the planar edge-count argument. The graph universe is finite because the vertex type is finite; one can maximize edge sets among drawable supergraphs of `G`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_extension__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Set.Subset G.edgeSet H.edgeSet ∧
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K →
        Set.Subset H.edgeSet K.edgeSet →
        H.edgeSet = K.edgeSet := by sorry
