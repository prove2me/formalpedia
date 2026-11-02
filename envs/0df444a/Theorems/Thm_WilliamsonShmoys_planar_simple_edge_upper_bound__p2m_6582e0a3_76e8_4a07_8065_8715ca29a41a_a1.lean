-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
-- name    : WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:04.465205+00:00
-- url     : https://prove2.me/theorems/2120accc-e77c-4707-8c72-d7b3ece39068
-- title:
--   Simple planar edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
