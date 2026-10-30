-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:02:54.173992+00:00
-- url     : https://prove2.me/theorems/177235df-d80e-42d3-b015-184b24262b4a
-- title:
--   Simple planar graph edge bound
-- statement:
--   A simple graph with at least three vertices and a drawing satisfying the given planar drawing predicate has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
