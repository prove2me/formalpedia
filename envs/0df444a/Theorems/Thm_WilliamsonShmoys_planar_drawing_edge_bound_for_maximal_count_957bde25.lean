-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_maximal_count_957bde25
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:39:28.889452+00:00
-- url     : https://prove2.me/theorems/f12a69bf-0e8d-45a5-8cf0-59db52a03d9f
-- title:
--   Planar drawings satisfy the simple graph edge bound
-- statement:
--   A finite simple graph with the supplied crossing-free drawing predicate and at least three vertices has at most 3|V|−6 edges. The size hypothesis is retained, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
