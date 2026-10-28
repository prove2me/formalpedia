-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_c3d7847a
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_c3d7847a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:31:54.454699+00:00
-- url     : https://prove2.me/theorems/cb3a57e5-88e3-48c5-93b5-bb4cb8a09eab
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph with no drawable strict supergraph. Maximize edge-set cardinality among the finitely many supergraphs that contain the given graph; this collection is nonempty because it contains the given graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_c3d7847a
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet = J.edgeSet := by sorry
