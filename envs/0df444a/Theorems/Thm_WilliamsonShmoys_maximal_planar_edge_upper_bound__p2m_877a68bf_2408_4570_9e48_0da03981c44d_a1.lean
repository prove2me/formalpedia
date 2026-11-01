-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:04:15.830462+00:00
-- url     : https://prove2.me/theorems/3afafa65-8e09-4130-830e-45057f389001
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges, stated without natural-number subtraction as |E| + 6 ≤ 3|V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_877a68bf_2408_4570_9e48_0da03981c44d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
