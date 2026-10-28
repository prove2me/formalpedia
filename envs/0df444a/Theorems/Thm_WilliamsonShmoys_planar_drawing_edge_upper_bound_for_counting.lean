-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_for_counting
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_for_counting
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:08:31.6475+00:00
-- url     : https://prove2.me/theorems/1f26b2b1-f51b-4e13-bfd7-806af5753a70
-- title:
--   Planar drawing edge upper bound for counting
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_for_counting {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : (K.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
