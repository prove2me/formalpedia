-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:15.10669+00:00
-- url     : https://prove2.me/theorems/81563a54-65ad-41c2-b8fa-9b4ca4b4c4bf
-- title:
--   Edge count for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has at least 3|V|−6 edges. At |V| = 3 this requires at least 3 edges; maximality rules out omitting any edge of the triangle. For larger vertex sets, the independent proof route is the standard planar maximality argument: maximality rules out disconnected components and faces with more than three boundary edges, after which Euler’s formula gives the edge count. This isolates the drawing-to-edge-count argument from the finite maximal-extension choice in the other child; the topological maximality argument remains to be formalized.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ H : SimpleGraph V, L ≤ H → HasPlanarDrawingOn H → H = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
