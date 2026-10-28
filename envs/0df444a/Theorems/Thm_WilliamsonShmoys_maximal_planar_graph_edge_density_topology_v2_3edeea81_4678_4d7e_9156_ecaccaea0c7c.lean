-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_density_topology_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_density_topology_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:55:31.066794+00:00
-- url     : https://prove2.me/theorems/5f43c2c9-3cd6-456f-b8c5-ff0269deed48
-- title:
--   An inclusion-maximal drawable graph meets the planar edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_edge_density_topology_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
