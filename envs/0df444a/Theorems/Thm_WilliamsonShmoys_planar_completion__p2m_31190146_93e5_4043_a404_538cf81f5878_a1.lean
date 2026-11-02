-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion__p2m_31190146_93e5_4043_a404_538cf81f5878_a1
-- name    : WilliamsonShmoys.planar_completion__p2m_31190146_93e5_4043_a404_538cf81f5878_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:54:34.360699+00:00
-- url     : https://prove2.me/theorems/9bfda91a-9bda-408b-a2fd-6ab368fb7e28
-- title:
--   Drawable graphs extend to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion__p2m_31190146_93e5_4043_a404_538cf81f5878_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
