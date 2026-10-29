-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
-- name    : WilliamsonShmoys.planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:43:17.436014+00:00
-- url     : https://prove2.me/theorems/d4f28163-3042-4d0d-a07e-fef5f41a3e54
-- title:
--   Simple planar edge bound
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most 3n−6 edges, expressed without natural-number subtraction. This supplies the quantitative bound that turns Euler’s identity into the parent’s face inequality. A proof route is to count the two sides of each edge among face-boundary walks, show each face boundary has length at least three under these hypotheses, and combine that count with Euler’s identity. The vertex and connectedness assumptions rule out the small exceptional embedding with a boundary walk of length two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConnected : M.Connected) (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
