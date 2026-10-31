-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- name    : WilliamsonShmoys.planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:32:45.157986+00:00
-- url     : https://prove2.me/theorems/0268dd7c-b22a-4ecf-a4e7-1329a8208a94
-- title:
--   Planar edge-count upper bound
-- statement:
--   A finite drawable simple graph on at least three vertices has at most 3n−6 edges. This supplies the upper bound for the completed supergraph; for n=3 it allows the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_bound__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
