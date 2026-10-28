-- Prove2me | Theorems.Thm_WilliamsonShmoys_has_planar_drawing_on_connected_supergraph_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
-- name    : WilliamsonShmoys.has_planar_drawing_on_connected_supergraph_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:26:54.258448+00:00
-- url     : https://prove2.me/theorems/50ac38a7-9b82-4fb4-8c14-f392c3fb0320
-- title:
--   Connect a drawn planar graph by adding edges
-- statement:
--   A drawn planar graph with at least three vertices can be enlarged on the same vertex type to a connected graph while retaining its edges and a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.has_planar_drawing_on_connected_supergraph_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
