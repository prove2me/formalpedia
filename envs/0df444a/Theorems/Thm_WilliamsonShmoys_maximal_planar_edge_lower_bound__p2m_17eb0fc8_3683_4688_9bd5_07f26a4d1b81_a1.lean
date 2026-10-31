-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:59.00312+00:00
-- url     : https://prove2.me/theorems/e98f9a30-577d-4730-aed3-8f09e7d6352a
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A drawable graph that is maximal under drawable supergraphs on the same vertex type has at least 3n−6 edges. The standard route augments the drawing inside nontriangular faces until it is triangulated; maximality forces the original graph to already have the maximal edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * (Fintype.card V - 2) ≤ K.edgeSet.ncard := by sorry
