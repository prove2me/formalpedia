-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_for_edge_bound_584c8b76
-- name    : WilliamsonShmoys.maximal_planar_face_equations_for_edge_bound_584c8b76
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:20:23.717985+00:00
-- url     : https://prove2.me/theorems/e944d3e8-7548-4f5d-a03a-092053315793
-- title:
--   Euler and triangular-face equations for maximal planar drawings
-- statement:
--   For a drawable finite graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set, there is a natural number of faces satisfying Euler’s equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_equations_for_edge_bound_584c8b76
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
