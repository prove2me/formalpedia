-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_via_euler_a4779231
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound_via_euler_a4779231
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:57:41.800814+00:00
-- url     : https://prove2.me/theorems/00042290-9a39-45b2-92de-9836869397f6
-- title:
--   Simple planar graph edge bound from Euler’s formula
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound_via_euler_a4779231
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
