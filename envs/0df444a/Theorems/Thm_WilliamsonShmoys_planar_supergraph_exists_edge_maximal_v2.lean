-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_edge_maximal_v2
-- name    : WilliamsonShmoys.planar_supergraph_exists_edge_maximal_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:14:01.988254+00:00
-- url     : https://prove2.me/theorems/46011126-edfc-46e8-9366-f5b4eeb06440
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type whose edge set is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_exists_edge_maximal_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Set.Subset P.edgeSet Q.edgeSet ∧
      ∀ R : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn R →
        Set.Subset Q.edgeSet R.edgeSet →
        R.edgeSet = Q.edgeSet := by sorry
