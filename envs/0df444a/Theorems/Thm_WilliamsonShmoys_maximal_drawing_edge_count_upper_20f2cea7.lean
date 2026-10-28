-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_upper_20f2cea7
-- name    : WilliamsonShmoys.maximal_drawing_edge_count_upper_20f2cea7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:38:53.938602+00:00
-- url     : https://prove2.me/theorems/3772f93c-87b6-4633-b1ce-7bbdd56fe0a4
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Any graph with the specified crossing-free drawing and at least three vertices has at most `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_edge_count_upper_20f2cea7
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
