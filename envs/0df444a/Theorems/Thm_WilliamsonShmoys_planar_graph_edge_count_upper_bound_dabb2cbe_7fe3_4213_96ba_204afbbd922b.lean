-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:24:47.734314+00:00
-- url     : https://prove2.me/theorems/c93b9b21-e4d3-42f0-9dd3-f674031d7b25
-- title:
--   Drawable graph planar edge-count upper bound
-- statement:
--   Every graph admitting the specified planar drawing, with at least three vertices, has at most 3|V| − 6 edges. Connect planar components if needed, then use Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound_dabb2cbe_7fe3_4213_96ba_204afbbd922b
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
