-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_equations_finite_maximal_extension
-- name    : WilliamsonShmoys.face_equations_finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:13:59.748764+00:00
-- url     : https://prove2.me/theorems/48b69916-5780-4741-812b-fc41fe4af2dd
-- title:
--   Finite maximal drawable extension
-- statement:
--   Any drawable graph on a finite ordered vertex type has a drawable supergraph that has no strict drawable edge supergraph on the same vertices. Choose a drawable supergraph with the largest edge count among the finite collection; a strict extension would have more edges. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.face_equations_finite_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N.edgeSet ⊂ K.edgeSet → ¬ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
