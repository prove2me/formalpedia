-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_of_connected_subgraph
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_of_connected_subgraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:08:36.772823+00:00
-- url     : https://prove2.me/theorems/79bba284-f932-49fa-aed3-2669b6357e0d
-- title:
--   Planar triangulation extension of a connected supergraph
-- statement:
--   A planar graph containing a connected spanning subgraph on at least three vertices can be extended, without adding vertices, to a planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_of_connected_subgraph
    {V : Type} [Fintype V] [LinearOrder V]
    (J K : SimpleGraph V)
    (hJK : J.edgeSet ⊆ K.edgeSet)
    (hConn : J.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
