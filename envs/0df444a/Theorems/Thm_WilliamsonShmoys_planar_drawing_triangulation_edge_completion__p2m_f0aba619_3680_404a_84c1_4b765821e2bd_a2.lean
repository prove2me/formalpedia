-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_completion__p2m_f0aba619_3680_404a_84c1_4b765821e2bd_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_edge_completion__p2m_f0aba619_3680_404a_84c1_4b765821e2bd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:39:04.797377+00:00
-- url     : https://prove2.me/theorems/533c1536-70f9-4baf-8d8d-aa7e4273cff9
-- title:
--   Triangulated planar supergraph with the maximal edge count
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices has a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6, and the original graph’s edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_edge_completion__p2m_f0aba619_3680_404a_84c1_4b765821e2bd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
