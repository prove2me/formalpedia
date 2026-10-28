-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_equations_maximal_planar_edge_count_lower_bound
-- name    : WilliamsonShmoys.face_equations_maximal_planar_edge_count_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:19:50.565207+00:00
-- url     : https://prove2.me/theorems/c982a1cd-90c0-4c9c-8f04-93f14c52998d
-- title:
--   Maximal planar edge-count lower bound for face equations
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same finite vertex type, with at least three vertices, has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.face_equations_maximal_planar_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
