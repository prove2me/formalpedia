-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_completion__p2m_128bf6bf_2a09_471e_9b1c_d385c868d715_a1
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_completion__p2m_128bf6bf_2a09_471e_9b1c_d385c868d715_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:47:00.341002+00:00
-- url     : https://prove2.me/theorems/8c6a7d59-3d50-48bd-989b-b7738f5488ee
-- title:
--   Every drawable graph has a triangulated planar completion
-- statement:
--   For a drawable simple graph on a finite linearly ordered vertex type with at least three vertices, there is a drawable supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulation_completion__p2m_128bf6bf_2a09_471e_9b1c_d385c868d715_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
