-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_data
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:02:43.910799+00:00
-- url     : https://prove2.me/theorems/3cb44ee4-40a7-4b24-9eb3-7742e5d75ae2
-- title:
--   Triangular face data for a maximal planar drawing
-- statement:
--   Every maximal drawable simple graph on at least three vertices has finite face data satisfying Euler’s relation, the edge-face incidence count, and triangularity of every face. This packages the topological core needed by the parent; proving it requires constructing the face model from the custom drawing and showing maximality forces triangular boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (instF : Fintype F) (boundaryLength : F → ℕ),
      Fintype.card V + @Fintype.card F instF = H.edgeSet.ncard + 2 ∧
      (@Finset.univ F instF).sum boundaryLength = 2 * H.edgeSet.ncard ∧
      ∀ f, boundaryLength f = 3 := by sorry
