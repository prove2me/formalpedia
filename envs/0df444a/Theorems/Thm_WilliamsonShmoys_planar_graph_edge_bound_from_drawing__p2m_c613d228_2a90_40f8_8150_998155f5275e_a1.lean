-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1
-- name    : WilliamsonShmoys.planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:45:25.657255+00:00
-- url     : https://prove2.me/theorems/c5eab97f-571a-4af4-85c9-353e33d2f94f
-- title:
--   Euler edge bound for finite drawn planar graphs
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most 3|V| − 6 edges, regardless of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_bound_from_drawing__p2m_c613d228_2a90_40f8_8150_998155f5275e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
