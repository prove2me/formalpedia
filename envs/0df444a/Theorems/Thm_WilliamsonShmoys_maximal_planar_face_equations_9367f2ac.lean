-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_9367f2ac
-- name    : WilliamsonShmoys.maximal_planar_face_equations_9367f2ac
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:58:10.209387+00:00
-- url     : https://prove2.me/theorems/43062042-0cdc-4c51-9c62-1a9950b577b3
-- title:
--   Euler and triangular-face equations for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has a number of faces satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_equations_9367f2ac
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
