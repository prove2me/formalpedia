-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:24:29.347921+00:00
-- url     : https://prove2.me/theorems/8d118255-640d-459b-9d55-e13b141f8172
-- title:
--   A maximal drawable graph has the maximal planar edge count
-- statement:
--   If a drawable simple graph on at least three vertices has no strict drawable supergraph on the same vertex type, then it has exactly 3|V|−6 edges. Maximality forces a triangulation: any face that can be further divided by a permissible edge would give a strict drawable supergraph. Counting triangular faces with Euler’s formula yields the equality; the lower bound |V| ≥ 3 covers the triangle boundary case and makes the natural-number subtraction well behaved. This child isolates the main topological and Euler-counting work from the finite maximal-choice argument. Its remaining core obligation is to justify triangulation and the face count for drawings represented by the given arc predicate, including cut vertices and disconnected candidates before maximality forces connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, L ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L) : 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
