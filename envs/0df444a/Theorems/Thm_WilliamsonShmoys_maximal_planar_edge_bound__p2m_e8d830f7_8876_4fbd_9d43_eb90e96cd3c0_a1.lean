-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:58.911055+00:00
-- url     : https://prove2.me/theorems/33fd9cf6-5dff-42ab-8e0f-e49b055267c2
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel _;
     3 * Fintype.card V - 6 <= H.edgeFinset.card) := by sorry
