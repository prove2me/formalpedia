-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_completion_exists
-- name    : WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_completion_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:51:05.236082+00:00
-- url     : https://prove2.me/theorems/a2b86923-b6a2-48bd-8026-df741a29ff00
-- title:
--   Existence of an edge-maximal planar drawing completion
-- statement:
--   Every graph with a drawing as defined in the imported predicate has a same-vertex edge-maximal drawable supergraph, and its edge count is at least the original graph's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_completion_exists {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H) ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
