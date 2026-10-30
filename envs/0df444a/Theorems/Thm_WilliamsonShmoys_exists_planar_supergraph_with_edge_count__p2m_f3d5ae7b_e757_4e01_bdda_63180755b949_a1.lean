-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:21:16.746211+00:00
-- url     : https://prove2.me/theorems/56ff2e59-7339-4433-a91a-44d558d3726b
-- title:
--   Planar supergraph completion with the triangulation edge count
-- statement:
--   Any finite simple graph with a crossing-free planar drawing and at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
