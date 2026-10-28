-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_ea237986_dde8_45aa_8717_82b33fafcc6c
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_ea237986_dde8_45aa_8717_82b33fafcc6c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:00:00.269284+00:00
-- url     : https://prove2.me/theorems/efb53ae9-56ba-4f02-bc1c-73bf2f95b7a7
-- title:
--   Planar simple graph edge bound for this drawing predicate
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most 3n−6 edges. The standard proof counts both incidences of each edge in facial boundary walks, including bridges, and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_ea237986_dde8_45aa_8717_82b33fafcc6c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
