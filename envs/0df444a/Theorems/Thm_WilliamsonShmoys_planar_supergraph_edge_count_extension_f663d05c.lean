-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_extension_f663d05c
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_extension_f663d05c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:59:46.802922+00:00
-- url     : https://prove2.me/theorems/4d8f612f-5d9b-4a14-abf6-2aa74f72eb02
-- title:
--   Extend a planar drawing to a graph with the triangulation edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three is a subgraph of a crossing-free graph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_count_extension_f663d05c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
