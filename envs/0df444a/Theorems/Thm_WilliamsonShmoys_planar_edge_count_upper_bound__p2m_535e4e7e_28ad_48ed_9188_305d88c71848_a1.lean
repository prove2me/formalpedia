-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:03:05.208472+00:00
-- url     : https://prove2.me/theorems/56609264-6a9a-4229-a716-b7a8ddd670b3
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any drawable simple graph on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
