-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_subgraph_edge_bound_of_connected_planar_supergraph
-- name    : WilliamsonShmoys.planar_subgraph_edge_bound_of_connected_planar_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:14:08.735682+00:00
-- url     : https://prove2.me/theorems/61ca263b-415e-46d9-a83e-57fd1a8a1974
-- title:
--   Edge bound inherited from a connected planar supergraph
-- statement:
--   A graph on at least three vertices inherits the planar edge bound from any connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_subgraph_edge_bound_of_connected_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V)
    (hGH : G ≤ H) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
