-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_ws_v2
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph_ws_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:52:10.807276+00:00
-- url     : https://prove2.me/theorems/755f9310-38b1-458a-96fe-c2339568d381
-- title:
--   Drawable graph has a triangulated planar extension
-- statement:
--   A finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges. This handles disconnected starting graphs as well as connected ones.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph_ws_v2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ 3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
