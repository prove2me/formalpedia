-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_v2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_v2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T01:56:46.316539+00:00
-- url     : https://prove2.me/theorems/536c6c85-cbc4-4673-b680-3be8a60c3c41
-- title:
--   Connecting components of a planar drawing
-- statement:
--   A finite graph with a crossing-free drawing can be extended on the same vertex set to a connected graph that still has a crossing-free drawing and has at least as many edges. This removes the disconnected case from the parent; an independent route is to connect drawing components successively with arcs whose interiors avoid the existing finite drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
