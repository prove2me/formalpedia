-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_le
-- name    : WilliamsonShmoys.planar_simple_graph_edge_count_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:58:38.314991+00:00
-- url     : https://prove2.me/theorems/4362522d-a11c-4289-bbd8-91c4db91a7e6
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   A simple graph on at least three finite vertices with a crossing-free planar drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_count_le
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V) :
    P.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
