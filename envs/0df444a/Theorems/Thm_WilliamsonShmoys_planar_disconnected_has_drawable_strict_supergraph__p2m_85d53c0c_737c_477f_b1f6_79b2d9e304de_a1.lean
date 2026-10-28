-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_drawable_strict_supergraph__p2m_85d53c0c_737c_477f_b1f6_79b2d9e304de_a1
-- name    : WilliamsonShmoys.planar_disconnected_has_drawable_strict_supergraph__p2m_85d53c0c_737c_477f_b1f6_79b2d9e304de_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:24:35.118988+00:00
-- url     : https://prove2.me/theorems/f334ebf7-af6a-4731-b73d-7440fcdb3338
-- title:
--   A disconnected drawable graph admits a strict drawable supergraph
-- statement:
--   If a drawable graph on at least two vertices is disconnected, it has a strict supergraph on the same vertices that is also drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_has_drawable_strict_supergraph__p2m_85d53c0c_737c_477f_b1f6_79b2d9e304de_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 2 ≤ Fintype.card V)
    (hNot : ¬ K.Connected) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ K := by sorry
