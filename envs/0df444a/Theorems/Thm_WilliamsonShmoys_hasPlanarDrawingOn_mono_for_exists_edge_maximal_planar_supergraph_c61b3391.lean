-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono_for_exists_edge_maximal_planar_supergraph_c61b3391
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono_for_exists_edge_maximal_planar_supergraph_c61b3391
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:23:00.541276+00:00
-- url     : https://prove2.me/theorems/eea97233-9e38-4c07-b037-0a24b39743a1
-- title:
--   Restricting a planar drawing to a subgraph
-- statement:
--   A subgraph of a graph with a crossing-free drawing inherits a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono_for_exists_edge_maximal_planar_supergraph_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : HasPlanarDrawingOn H) :
    HasPlanarDrawingOn G := by sorry
