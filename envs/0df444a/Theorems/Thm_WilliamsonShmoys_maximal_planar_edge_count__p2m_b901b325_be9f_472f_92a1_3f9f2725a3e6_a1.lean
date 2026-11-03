-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:02:25.221167+00:00
-- url     : https://prove2.me/theorems/f879e044-377f-46b9-9503-40e9e2d9cd50
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b901b325_be9f_472f_92a1_3f9f2725a3e6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
