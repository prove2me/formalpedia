-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_supergraph_edge_bound__p2m_abc6942a_8a99_4355_badf_59d2c1ffe2f0_a1
-- name    : WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_abc6942a_8a99_4355_badf_59d2c1ffe2f0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:45:08.510994+00:00
-- url     : https://prove2.me/theorems/f480263f-1ac3-4297-8888-36232c8b7a10
-- title:
--   Planar supergraph edge lower bound by triangulation
-- statement:
--   Any finite simple graph with at least three vertices that admits the specified crossing-free drawing has a planar supergraph on the same vertices with at least 3|V| - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_abc6942a_8a99_4355_badf_59d2c1ffe2f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, M <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  sorry
