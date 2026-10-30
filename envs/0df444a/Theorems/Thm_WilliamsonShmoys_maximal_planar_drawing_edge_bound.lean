-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:48:00.511117+00:00
-- url     : https://prove2.me/theorems/5f9d6e14-aa4e-49d5-9b5f-a95bf0094730
-- title:
--   Edge bound for a maximal drawn planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
