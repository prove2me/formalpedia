-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_upper_bound
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:10:10.40272+00:00
-- url     : https://prove2.me/theorems/a67f12a4-d905-496e-b2ba-b71bf100c45a
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A finite simple graph on at least three vertices admitting the specified planar drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
