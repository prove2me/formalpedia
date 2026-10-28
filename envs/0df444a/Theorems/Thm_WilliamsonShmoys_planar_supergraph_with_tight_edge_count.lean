-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_tight_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_with_tight_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:26:26.176272+00:00
-- url     : https://prove2.me/theorems/ea3c3bca-e9d3-46c1-a6df-edf59f062e04
-- title:
--   A drawable graph extends to a tight planar supergraph
-- statement:
--   Every graph with a crossing-free drawing on a fixed finite ordered vertex type of size at least three is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_tight_edge_count {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
