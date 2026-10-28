-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_41b75d1a
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_41b75d1a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T14:49:26.749513+00:00
-- url     : https://prove2.me/theorems/b70ed9b8-ea62-476e-b378-d22b98f4e8f9
-- title:
--   Euler upper bound for a finite planar drawing
-- statement:
--   Any graph with a drawing satisfying the supplied crossing-free arc definition has at most three times its vertex count minus six edges when there are at least three vertices. This isolates the Euler upper-bound direction. A proof route is to pass from the finite drawing to a plane graph, account for disconnected components and isolated vertices, and apply Euler's formula with the face-degree bound. The lower-size hypothesis covers the smallest allowed case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_41b75d1a
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
