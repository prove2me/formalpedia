-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:35:32.09009+00:00
-- url     : https://prove2.me/theorems/e13857bb-dfd7-4e7a-a1e7-eab5feffe183
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A drawable simple graph with at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [DecidableRel L.Adj] (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) : L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
