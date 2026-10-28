-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_for_edgeCount_completion
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edgeCount_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:02:13.901242+00:00
-- url     : https://prove2.me/theorems/f10545bd-fbc4-4fc9-8d51-83cb94343a4d
-- title:
--   A planar drawing has an edge-maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edgeCount_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.IsPlanarMaximalSupergraphForEdgeCountCompletion U W := by sorry
