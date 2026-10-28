-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:47:28.607794+00:00
-- url     : https://prove2.me/theorems/0359c2de-483c-4e08-9117-cd9dcde287a8
-- title:
--   Planar edge-count upper bound
-- statement:
--   A finite drawable simple graph with at least three vertices has at most 3|V| − 6 edges, whether connected or disconnected. This removes the Euler upper-bound argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_job_09cd0f78_596e_4a94_9326_038b3be8d638
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
