-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_faces_certificate
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_faces_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:31:40.558279+00:00
-- url     : https://prove2.me/theorems/2ed2d229-9474-41ef-b2a0-00d05dcb5fde
-- title:
--   Euler and face-incidence certificate for a maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices that is inclusion-maximal among graphs on the same vertex type admitting the given crossing-free drawing has a face count satisfying both the edge-face incidence identity and Euler’s formula. The lower bound is needed to rule out the small-vertex exceptions. Prove this by deriving connectedness and triangular faces from maximality, then formalizing face traversal and Euler counting. This removes the final numerical elimination from the parent while leaving the topological counting argument as the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_euler_faces_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    ∃ f : ℕ,
      2 * L.edgeSet.ncard = 3 * f ∧
      Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
