-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- name    : WilliamsonShmoys.planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:28:28.492993+00:00
-- url     : https://prove2.me/theorems/09fd82f6-9481-4fe8-ab66-93ef18097a0d
-- title:
--   Planar edge bound for a finite drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
