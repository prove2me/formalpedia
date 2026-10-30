-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing
-- name    : WilliamsonShmoys.planar_edge_bound_of_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:08:29.11992+00:00
-- url     : https://prove2.me/theorems/5be0e446-5676-4591-ad5c-6c470f2261db
-- title:
--   Euler edge bound for a planar drawing
-- statement:
--   A drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
