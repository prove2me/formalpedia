-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2_aux_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_v2_aux_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:38:16.105466+00:00
-- url     : https://prove2.me/theorems/dcdbc4bf-3649-4f03-bf4e-e9bc5948f906
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_v2_aux_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    W.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
