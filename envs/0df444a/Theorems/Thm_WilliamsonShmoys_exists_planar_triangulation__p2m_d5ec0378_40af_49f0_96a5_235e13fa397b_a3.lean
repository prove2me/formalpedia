-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
-- name    : WilliamsonShmoys.exists_planar_triangulation__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T06:05:00.611985+00:00
-- url     : https://prove2.me/theorems/c5383de8-4fc8-4031-bbce-845eb65f9b8d
-- title:
--   A drawn triangulation on every finite vertex type
-- statement:
--   Every finite linearly ordered vertex type with at least three elements admits a connected simple graph on exactly that type, with a drawing satisfying `HasPlanarDrawingOn` and exactly `3 * card V - 6` edges. A convex polygon fan triangulation supplies the construction, including the three-vertex triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
