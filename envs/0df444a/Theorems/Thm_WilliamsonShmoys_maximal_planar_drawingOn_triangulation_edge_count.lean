-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_triangulation_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:12:39.579876+00:00
-- url     : https://prove2.me/theorems/26688f3c-2bfa-482b-811b-fcb8201596ad
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
