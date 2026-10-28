-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_equations_edge_formula
-- name    : WilliamsonShmoys.face_count_equations_edge_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:44:38.619298+00:00
-- url     : https://prove2.me/theorems/e082ec66-7fbc-4853-ae67-5244318e4cd5
-- title:
--   Edge formula from face-count equations
-- statement:
--   Euler’s equation and the triangular-face incidence equation imply the maximal planar edge-count formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.face_count_equations_edge_formula
    {V : Type} [Fintype V] {L : SimpleGraph V}
    (f : ℕ)
    (hEuler : L.edgeSet.ncard + 2 = Fintype.card V + f)
    (hIncidence : 3 * f = 2 * L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
