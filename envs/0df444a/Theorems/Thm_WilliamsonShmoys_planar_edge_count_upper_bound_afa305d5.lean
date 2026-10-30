-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_afa305d5
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_afa305d5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:45:54.633751+00:00
-- url     : https://prove2.me/theorems/0bf22796-9de1-4d9e-b4b6-caf4eeb64944
-- title:
--   Edge bound for a drawable graph
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V| − 6 edges. This supplies the upper bound for the target without using maximality. It preserves the three-vertex cutoff: at |V| = 3, the inequality permits at most three edges. A proof route is to obtain an embedding from the drawing, apply Euler’s formula with face-boundary counting, and handle disconnected components in the edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_afa305d5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
