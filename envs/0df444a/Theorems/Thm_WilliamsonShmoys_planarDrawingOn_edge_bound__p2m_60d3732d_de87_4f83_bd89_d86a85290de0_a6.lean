-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edge_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- name    : WilliamsonShmoys.planarDrawingOn_edge_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:44.911693+00:00
-- url     : https://prove2.me/theorems/9d34f080-ed68-445b-bb08-ad40d7fc216e
-- title:
--   Simple planar graphs satisfy the edge bound
-- statement:
--   For a finite simple graph on at least three vertices, a crossing-free drawing by the supplied continuous arcs implies the planar edge bound. This removes the geometric planarity work needed by the parent. A proof route is the standard Euler edge-count argument for a simple planar graph, applied to the drawing encoded by `HasPlanarDrawingOn`; the exact arc injectivity and intersection hypotheses provide the drawing conventions required by that theorem. The bound is valid at the equality boundary, for example for a triangulation such as K₃ or K₄.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_edge_bound__p2m_60d3732d_de87_4f83_bd89_d86a85290de0_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
