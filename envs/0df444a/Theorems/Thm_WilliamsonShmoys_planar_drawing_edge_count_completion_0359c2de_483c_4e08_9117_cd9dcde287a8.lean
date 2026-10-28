-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_0359c2de_483c_4e08_9117_cd9dcde287a8
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_0359c2de_483c_4e08_9117_cd9dcde287a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:01:50.505506+00:00
-- url     : https://prove2.me/theorems/cbd57c51-e334-4f4e-814f-42afaa7d171b
-- title:
--   Planar completion with the maximal edge count
-- statement:
--   A drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_0359c2de_483c_4e08_9117_cd9dcde287a8
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
