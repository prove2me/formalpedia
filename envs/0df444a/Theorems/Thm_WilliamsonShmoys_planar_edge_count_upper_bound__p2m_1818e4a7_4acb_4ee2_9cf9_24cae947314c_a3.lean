-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:01.07621+00:00
-- url     : https://prove2.me/theorems/004e5ed5-cd67-44f8-b54c-b7b595ba6dfb
-- title:
--   Planar simple graph edge bound
-- statement:
--   A simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most 3|V| − 6 edges. This isolates the general planar edge bound used by the parent. A proof route uses Euler’s formula and face-edge incidence counting on connected components, treating tree components separately; the size hypothesis supplies the range in which the bound holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
