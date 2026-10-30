-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:23:49.555948+00:00
-- url     : https://prove2.me/theorems/04e06949-830f-4934-a0e9-adbd2a0cf4ea
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   A crossing-free drawing of a finite simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
