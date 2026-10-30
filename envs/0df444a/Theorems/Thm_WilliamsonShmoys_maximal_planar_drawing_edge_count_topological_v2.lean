-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_topological_v2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_topological_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:42:39.575956+00:00
-- url     : https://prove2.me/theorems/3227e606-20d5-40ad-890c-f15e352b446e
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal simple graph with a crossing-free drawing on a finite linearly ordered vertex type and at least three vertices has exactly `3|V| − 6` edges. This removes the topological edge-count argument from the parent; a proof route is to show maximality forces a connected triangulation, then apply Euler’s formula and count incidences between edges and faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_topological_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : forall W : SimpleGraph V,
      LE.le U W -> WilliamsonShmoys.HasPlanarDrawingOn W -> W = U)
    (hV : 3 <= Fintype.card V) :
    U.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
