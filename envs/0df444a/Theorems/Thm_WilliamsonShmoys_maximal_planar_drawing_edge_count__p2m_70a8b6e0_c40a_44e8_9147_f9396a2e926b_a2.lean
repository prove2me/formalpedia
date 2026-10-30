-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:55.635859+00:00
-- url     : https://prove2.me/theorems/84f2d88d-c1bb-48f4-b85d-8d668d11d624
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is inclusion-maximal among drawable supergraphs on its vertex type has exactly 3n−6 edges. This isolates the parent’s topological and Euler-counting obligation. A proof route is to establish that maximality forces a connected triangulation, then use Euler’s formula and count each face-edge incidence twice. The condition of at least three vertices is preserved because the exact maximal-planar edge-count formula needs it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
