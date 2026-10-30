-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion__p2m_536aaf66_0a7c_4c8d_b8d1_73a7e039d5bd_a2
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_536aaf66_0a7c_4c8d_b8d1_73a7e039d5bd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T02:20:58.526983+00:00
-- url     : https://prove2.me/theorems/41e7410d-5f15-47e2-b0be-551bd25b1c53
-- title:
--   Exact edge-count completion for a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex set with exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_536aaf66_0a7c_4c8d_b8d1_73a7e039d5bd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
