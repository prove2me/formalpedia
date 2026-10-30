-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_completion_36583a35_retry3
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_completion_36583a35_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:12:43.092483+00:00
-- url     : https://prove2.me/theorems/e9be8b0d-e783-413e-8020-036dd367062a
-- title:
--   Drawable graphs have an exact maximal planar completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges. The boundary case of three vertices is completed to the triangle. For larger sets, extend the drawing to a maximal planar drawing and use triangular faces, Euler’s formula, and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_exact_edge_completion_36583a35_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    exists K : SimpleGraph V,
      L <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
