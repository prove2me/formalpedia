-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:13:40.273747+00:00
-- url     : https://prove2.me/theorems/a8ac11fb-df56-48c4-b4e3-41b605b77449
-- title:
--   Euler edge count for a maximal planar graph
-- statement:
--   For a finite simple graph with at least three vertices, maximality among drawable supergraphs forces triangular faces; Euler’s formula and face-edge incidence then give the exact edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
