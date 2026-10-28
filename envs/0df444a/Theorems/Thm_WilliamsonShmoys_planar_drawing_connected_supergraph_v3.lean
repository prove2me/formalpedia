-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_v3
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:53:57.066735+00:00
-- url     : https://prove2.me/theorems/1352a525-73f5-4cdd-a9c1-32cb8628ec01
-- title:
--   Connecting components of a planar drawing on a nonempty vertex type
-- statement:
--   A finite graph on at least three vertices with a crossing-free drawing can be extended on the same vertex type to a connected graph that still has a crossing-free drawing and has at least as many edges. The nonempty-size hypothesis excludes the empty-type obstruction. One proof route is to join drawing components successively by simple arcs through the complement of the finite embedded graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
