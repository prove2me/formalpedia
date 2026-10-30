-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_face_counting_equations
-- name    : WilliamsonShmoys.maximal_drawable_face_counting_equations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:09:56.054968+00:00
-- url     : https://prove2.me/theorems/3bf5a307-a677-4652-af6f-9ad2cdab51c1
-- title:
--   Euler and face-incidence equations for a maximal drawable graph
-- statement:
--   For a drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_face_counting_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
