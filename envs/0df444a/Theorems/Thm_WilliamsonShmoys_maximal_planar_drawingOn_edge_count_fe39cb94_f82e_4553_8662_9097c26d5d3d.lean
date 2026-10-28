-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:54:07.99312+00:00
-- url     : https://prove2.me/theorems/fab67c4d-b652-4164-86ab-9a44998bea42
-- title:
--   Maximal drawable graph edge count
-- statement:
--   A drawable simple graph on at least three finite ordered vertices with no drawable strict edge supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
