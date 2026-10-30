-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:10:31.58597+00:00
-- url     : https://prove2.me/theorems/18d0d12d-5626-47c8-92da-bf1865e88ed0
-- title:
--   Edge lower bound for an edge-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable edge-set extension has at least 3n−6 edges. A proof route is to show maximality forces a connected triangulated embedding, then apply Euler’s formula and count the two sides of each edge. The n=3 case is included and gives equality for the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
