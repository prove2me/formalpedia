-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_for_edge_bound_562ccfc8
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_562ccfc8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:38:16.528363+00:00
-- url     : https://prove2.me/theorems/5af7d0ba-f8f8-49e1-967e-7e79b125326a
-- title:
--   Maximal planar supergraph on the same finite vertex type
-- statement:
--   A finite graph with a planar drawing has a planar supergraph on the same vertex type that is maximal among planar supergraphs. The finite family of simple graphs on V allows choosing a planar extension with maximal edge count. Any strict planar extension would add an edge and contradict that maximality. This argument works without a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_for_edge_bound_562ccfc8
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
