-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_face_count_equations
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_face_count_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:35:21.29087+00:00
-- url     : https://prove2.me/theorems/14998a38-c366-470e-b637-a7eb26ebed17
-- title:
--   Euler and incidence equations for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has a natural face count satisfying Euler’s equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_face_count_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    ∃ f : ℕ,
      L.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
