-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:08:53.047196+00:00
-- url     : https://prove2.me/theorems/93bdbff6-e557-4db5-883d-ea991796440f
-- title:
--   Euler edge bound for a drawable simple graph
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has at most three times its number of vertices minus six edges. The proof route is Euler’s formula on connected components, with separate estimates for components of size one or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_319863c5_d9cf_422f_8cc1_e579df5fd0de_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
