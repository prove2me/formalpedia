-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:55:09.19095+00:00
-- url     : https://prove2.me/theorems/453960ee-9f79-41a5-a937-fcd04f065b58
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite inclusion-maximal simple graph with a crossing-free drawing and at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
