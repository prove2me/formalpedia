-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:34.033711+00:00
-- url     : https://prove2.me/theorems/c80d2f01-7a07-4cb5-848a-3ed178dc77f9
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An edge-maximal graph with the specified planar drawing and at least three vertices has at least 3|V|−6 edges. A proof route is to complete the planar embedding to a triangulation using the same vertex set, show the completed graph remains planar and contains H, then apply the maximality hypothesis to identify it with H. Counting triangulation edges by Euler’s formula gives the bound. The same-vertex completion step must preserve the given drawing predicate; disconnected graphs and isolated vertices must be handled in that construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_d0cbf8fc_b126_4e9b_9c59_f16faa272cb9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ H' : SimpleGraph V, (∀ {u v : V}, H'.Adj u v → H.Adj u v) → HasPlanarDrawingOn H' → H' = H) : letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj; 3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by sorry
