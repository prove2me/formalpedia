-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_graph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
-- name    : WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:45:42.937242+00:00
-- url     : https://prove2.me/theorems/7842deb4-e63b-4553-baf8-30586367a025
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable supergraphs has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph_d8e86b30_fed1_4ee5_9c6d_8ff76555c4e7
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V)
    (hRmax : ∀ S : SimpleGraph V, R ≤ S →
      WilliamsonShmoys.HasPlanarDrawingOn S → S = R) :
    3 * Fintype.card V = R.edgeSet.ncard + 6 := by sorry
