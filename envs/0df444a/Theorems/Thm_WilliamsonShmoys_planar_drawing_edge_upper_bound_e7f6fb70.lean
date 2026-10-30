-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_e7f6fb70
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_e7f6fb70
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:13:38.620278+00:00
-- url     : https://prove2.me/theorems/c30650a9-dc9e-4e06-99f3-1cae8d07188c
-- title:
--   Euler edge bound for a planar drawing
-- statement:
--   A graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3n − 6` edges. This removes the upper-bound half of the target equality. A proof route is to derive a finite planar embedding from the drawing, apply Euler’s formula componentwise, and use simplicity to bound face boundary lengths. The stated lower bound on the vertex count handles the small-graph boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
