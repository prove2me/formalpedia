-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence
-- name    : WilliamsonShmoys.planar_drawing_face_incidence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:41:00.152275+00:00
-- url     : https://prove2.me/theorems/6feca42e-ad03-4029-9376-ed10e55a33cb
-- title:
--   Face-boundary incidence bound for a planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and the given planar drawing, any natural face count satisfying Euler’s equation obeys the aggregate face-boundary incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : K.edgeSet.ncard + 2 = Fintype.card V + f) :
    3 * f ≤ 2 * K.edgeSet.ncard := by sorry
