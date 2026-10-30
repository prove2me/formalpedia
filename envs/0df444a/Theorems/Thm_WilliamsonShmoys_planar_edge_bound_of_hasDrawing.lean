-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_hasDrawing
-- name    : WilliamsonShmoys.planar_edge_bound_of_hasDrawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:19:55.266685+00:00
-- url     : https://prove2.me/theorems/327da7f2-8632-4d60-af88-656093cb7e0b
-- title:
--   Euler edge bound for any finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges, regardless of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_of_hasDrawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
