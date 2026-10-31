-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:55.495504+00:00
-- url     : https://prove2.me/theorems/52ae77ae-f85b-40f5-bd03-34373df951b6
-- title:
--   Simple planar graph edge bound
-- statement:
--   For a finite simple graph with a drawing satisfying the supplied planar-drawing predicate and at least three vertices, the number of edges plus six is at most three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_1d9982e7_ae2e_41b5_99c8_f768b7d6d77d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
