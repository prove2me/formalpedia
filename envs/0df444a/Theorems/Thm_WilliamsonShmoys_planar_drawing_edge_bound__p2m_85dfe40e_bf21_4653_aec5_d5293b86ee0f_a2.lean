-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:41:20.590035+00:00
-- url     : https://prove2.me/theorems/7b8c7f37-b8de-44ac-bf27-503e942d415a
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   Every finite simple graph admitting the specified crossing-free drawing and having at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_85dfe40e_bf21_4653_aec5_d5293b86ee0f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
