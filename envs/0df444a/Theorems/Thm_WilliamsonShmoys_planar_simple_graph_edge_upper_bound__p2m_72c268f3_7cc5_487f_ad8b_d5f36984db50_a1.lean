-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:13.905959+00:00
-- url     : https://prove2.me/theorems/14c57b1a-9d57-45d2-8a0d-6125974ddbe0
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A drawable finite simple graph on at least three vertices has at most 3|V|−6 edges. This removes the general planar edge estimate from the parent; a route is Euler face counting, treating disconnected drawings and small face boundaries explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
