-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_counts__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:33.624691+00:00
-- url     : https://prove2.me/theorems/5f4b31de-07d6-4550-bc2e-2bb318dd0027
-- title:
--   Euler and face-degree counts for a maximal planar drawing
-- statement:
--   A maximal simple graph with a crossing-free drawing and at least three vertices has a face count satisfying Euler’s relation and the usual face-degree lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_counts__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  sorry
