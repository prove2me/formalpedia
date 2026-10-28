-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- name    : WilliamsonShmoys.planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:51:37.59105+00:00
-- url     : https://prove2.me/theorems/c0920f60-bc2d-4bb1-b296-43d9df7b59e0
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A simple graph with a planar drawing on at least three vertices has at most 3|V| − 6 edges. This is the upper-bound half of the target, independent of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
