-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_repair_20261027
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair_20261027
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:01:01.17457+00:00
-- url     : https://prove2.me/theorems/3f384705-7b5f-45d8-a8d4-8f9042cd10a9
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every simple graph with the packaged planar drawing predicate and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
