-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_planar_edge_extension_20261026
-- name    : WilliamsonShmoys.planar_disconnected_has_planar_edge_extension_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:43:10.220359+00:00
-- url     : https://prove2.me/theorems/48ae92f5-8a28-4345-9778-b029b12955d6
-- title:
--   A disconnected planar graph has a proper planar supergraph
-- statement:
--   If a graph on at least three vertices has a crossing-free drawing and is disconnected, it has a planar supergraph on the same vertices that is not a subgraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_planar_edge_extension_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ¬ L ≤ K := by sorry
