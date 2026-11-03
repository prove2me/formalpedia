-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:31:38.481108+00:00
-- url     : https://prove2.me/theorems/cd005786-48c0-47b3-9c83-f93270ee4ea9
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   A drawable simple graph with at least three vertices has at most 3|V|−6 edges, by Euler’s formula and the lower bound of three on face-boundary lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn N) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
