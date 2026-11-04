-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:36:38.625368+00:00
-- url     : https://prove2.me/theorems/abe63458-bbbb-493a-8df0-3e0f2c6fa377
-- title:
--   Maximal planarity forces the triangulated lower bound
-- statement:
--   A drawable simple graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_345280c0_3608_47c5_9d5e_5604ac889a3e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V ≤ H.edgeFinset.card + 6 := by sorry
