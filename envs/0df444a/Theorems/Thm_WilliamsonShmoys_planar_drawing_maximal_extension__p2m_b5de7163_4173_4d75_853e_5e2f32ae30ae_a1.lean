-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:06.888424+00:00
-- url     : https://prove2.me/theorems/3338048f-6efa-4f20-bc21-43d0f89dab18
-- title:
--   Maximal planar extension on the same vertex set
-- statement:
--   Every drawn planar graph on at least three vertices is contained, on the same vertex set, in a planar graph maximal under adding edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_b5de7163_4173_4d75_853e_5e2f32ae30ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet := by
  sorry
