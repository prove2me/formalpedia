-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_face_count_certificate
-- name    : WilliamsonShmoys.maximal_drawing_face_count_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:29:12.069953+00:00
-- url     : https://prove2.me/theorems/4e1a8ce7-d97b-4d15-ad77-83cfce372367
-- title:
--   Euler and triangular face counts for a maximal planar drawing
-- statement:
--   For a finite simple graph with at least three vertices, a drawing maximal among drawable supergraphs admits a face count satisfying Euler’s formula and the triangular face-edge incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_face_count_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    ∃ f : Nat,
      n + f = L.edgeSet.ncard + 2 ∧
      2 * L.edgeSet.ncard = 3 * f := by sorry
