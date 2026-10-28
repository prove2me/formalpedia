-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_54a0e51c
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_54a0e51c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:08:02.232041+00:00
-- url     : https://prove2.me/theorems/0ef6cdd6-0074-4ddf-9918-5e48acac88b4
-- title:
--   Euler edge bound for a drawable graph
-- statement:
--   A graph drawable in the plane on at least three vertices has at most 3n − 6 edges. The proof route is Euler’s formula, applied componentwise with separate handling for components of size one or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
