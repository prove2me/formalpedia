-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_for_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:39:28.029614+00:00
-- url     : https://prove2.me/theorems/da16a11a-5471-486c-94e9-448aef08e550
-- title:
--   Euler and triangular-face equations for a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same finite vertex type, with at least three vertices, has a face count satisfying Euler's equation and the triangular face-edge incidence equation. The vertex-count hypothesis is needed for the triangulation argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
