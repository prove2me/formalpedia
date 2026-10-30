-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_extension
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:26:50.388358+00:00
-- url     : https://prove2.me/theorems/ce2964ef-d768-4311-bdf9-21609deea6cd
-- title:
--   Extend a planar drawing to a maximal planar graph with 3n−6 edges
-- statement:
--   Any finite simple graph on at least three vertices with the supplied planar arc drawing is a subgraph of a graph on the same vertices with such a drawing and exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun L : SimpleGraph V => K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
