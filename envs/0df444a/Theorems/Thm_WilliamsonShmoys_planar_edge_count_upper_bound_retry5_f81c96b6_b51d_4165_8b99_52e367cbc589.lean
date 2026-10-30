-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_retry5_f81c96b6_b51d_4165_8b99_52e367cbc589
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_retry5_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:42:31.497041+00:00
-- url     : https://prove2.me/theorems/97473d55-1c54-47cc-b6c1-d782df0418a8
-- title:
--   Planar edge count upper bound for this target
-- statement:
--   Every graph with a crossing-free drawing on this finite ordered vertex type and at least three vertices has at most 3|V| − 6 edges, including when it is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_retry5_f81c96b6_b51d_4165_8b99_52e367cbc589
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
