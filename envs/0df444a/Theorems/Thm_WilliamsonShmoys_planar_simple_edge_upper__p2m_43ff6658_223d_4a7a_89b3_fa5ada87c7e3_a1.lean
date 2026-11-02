-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- name    : WilliamsonShmoys.planar_simple_edge_upper__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:12.049864+00:00
-- url     : https://prove2.me/theorems/ad7657d2-129c-4ff8-bf1d-16d96be983d7
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler-formula upper bound, independent of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_upper__p2m_43ff6658_223d_4a7a_89b3_fa5ada87c7e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
