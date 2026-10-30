-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulated_completion
-- name    : WilliamsonShmoys.exists_planar_triangulated_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:14:35.904045+00:00
-- url     : https://prove2.me/theorems/f17b4fc8-270a-4d90-afe8-2adc9402310a
-- title:
--   Completion of a planar drawing to a triangulation
-- statement:
--   Any planar drawing on a finite ordered vertex type with at least three vertices can be extended, on the same vertex type, to a planar graph with exactly 3n − 6 edges. This supplies the parent’s maximal planar completion; the remaining proof uses the parent hypothesis to show that the completion equals K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulated_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * n - 6 := by sorry
