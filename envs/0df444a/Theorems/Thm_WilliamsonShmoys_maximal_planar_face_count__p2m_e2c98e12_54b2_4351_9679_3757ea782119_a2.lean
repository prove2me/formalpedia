-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count__p2m_e2c98e12_54b2_4351_9679_3757ea782119_a2
-- name    : WilliamsonShmoys.maximal_planar_face_count__p2m_e2c98e12_54b2_4351_9679_3757ea782119_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:47.61292+00:00
-- url     : https://prove2.me/theorems/e138972d-9fa2-4192-8bee-87ee7300d413
-- title:
--   Face counts for a maximal drawable graph
-- statement:
--   A maximal drawable graph with at least three vertices has a face count satisfying Euler’s equation and the triangular-face incidence equation. Its drawing provides a plane embedding; maximality forces connectedness and triangular faces, with the three-vertex triangle as the boundary case. These equations yield the exact edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count__p2m_e2c98e12_54b2_4351_9679_3757ea782119_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      Set.Subset H.edgeSet K.edgeSet →
      H.edgeSet = K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by sorry
