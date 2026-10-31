-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:42.369991+00:00
-- url     : https://prove2.me/theorems/e2b82d88-2bbb-4150-bc2f-79d38f5c0ef7
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar simple graph on a finite vertex type with at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
