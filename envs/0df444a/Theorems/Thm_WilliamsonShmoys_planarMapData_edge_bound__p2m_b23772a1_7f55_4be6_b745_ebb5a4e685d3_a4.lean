-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarMapData_edge_bound__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a4
-- name    : WilliamsonShmoys.planarMapData_edge_bound__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:28.976838+00:00
-- url     : https://prove2.me/theorems/56c1a6aa-f1d2-43e3-a805-690e1f0ee863
-- title:
--   Derive the simple planar edge bound from face data
-- statement:
--   Face data recording Euler’s equation, total boundary incidence twice the edge count, and degree at least three for every face imply the simple planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planarMapData_edge_bound__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a4
    {V : Type} [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (D : PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 J) :
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
