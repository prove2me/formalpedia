-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_embedding
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_from_embedding
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:07:40.358129+00:00
-- url     : https://prove2.me/theorems/30cca0d0-b7c0-4d1d-9da7-1a010d7fc335
-- title:
--   Edge bound for a graph with a planar drawing
-- statement:
--   A finite simple graph with at least three vertices that admits the specified crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_from_embedding
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
