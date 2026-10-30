-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:17:12.813498+00:00
-- url     : https://prove2.me/theorems/c78caf9b-d4a4-445c-b3f0-7f02aee092ab
-- title:
--   Complete a drawable graph to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly the maximal planar edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
