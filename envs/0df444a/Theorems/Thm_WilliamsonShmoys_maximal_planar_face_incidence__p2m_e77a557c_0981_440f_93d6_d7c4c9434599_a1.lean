-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
-- name    : WilliamsonShmoys.maximal_planar_face_incidence__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:27.675047+00:00
-- url     : https://prove2.me/theorems/61dc9438-8340-4e4c-b1c7-250f3c9d3d5d
-- title:
--   Triangular face incidence count
-- statement:
--   For any face count satisfying Euler’s equation for this maximal drawing, triangular faces and two sides per edge give three face sides per face and two per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_incidence__p2m_e77a557c_0981_440f_93d6_d7c4c9434599_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K)
    (f : ℕ) (heuler : Fintype.card V + f = K.edgeSet.ncard + 2) :
    3 * f = 2 * K.edgeSet.ncard := by sorry
