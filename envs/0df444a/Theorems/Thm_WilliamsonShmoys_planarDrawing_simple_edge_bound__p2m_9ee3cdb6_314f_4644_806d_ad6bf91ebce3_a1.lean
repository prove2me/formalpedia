-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_simple_edge_bound__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- name    : WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:38.277205+00:00
-- url     : https://prove2.me/theorems/68659add-1ba6-4067-be65-c7b40be0a2e9
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple planar graph with at least three vertices has at most three times its vertex count minus six edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤
      3 * Fintype.card V := by sorry
