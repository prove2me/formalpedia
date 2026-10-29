-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:29:47.372263+00:00
-- url     : https://prove2.me/theorems/0d3ba6cc-be4a-436c-b614-289a3ecc8076
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_638a1f84_48cf_416d_8d32_57bed5d6bb46_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
