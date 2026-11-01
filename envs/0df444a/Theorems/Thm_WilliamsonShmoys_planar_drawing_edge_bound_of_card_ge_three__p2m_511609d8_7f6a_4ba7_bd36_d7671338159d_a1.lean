-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_card_ge_three__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_of_card_ge_three__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:05.611409+00:00
-- url     : https://prove2.me/theorems/6e9be569-c749-440b-898c-782fd4e92ed9
-- title:
--   Planar edge bound for at least three vertices
-- statement:
--   For a finite simple graph with a crossing-free drawing and at least three vertices, the number of edges is at most three times the number of vertices minus six. This isolates the Euler-formula argument that carries the main difficulty of the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_of_card_ge_three__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
