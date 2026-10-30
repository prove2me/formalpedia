-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_for_edge_lower_bound_9ae33b99
-- name    : WilliamsonShmoys.maximal_planar_face_equations_for_edge_lower_bound_9ae33b99
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:16:56.739283+00:00
-- url     : https://prove2.me/theorems/7d649107-ce1c-4212-b981-14f67890bc25
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A drawable simple graph with at least three vertices that is maximal among drawable supergraphs on the same vertex type has a finite face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_equations_for_edge_lower_bound_9ae33b99
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
