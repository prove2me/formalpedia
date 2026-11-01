-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:44.59946+00:00
-- url     : https://prove2.me/theorems/9d7178e3-993b-474e-9a8d-13a9e69ab77c
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every finite simple graph with a planar drawing has a planar supergraph on the same vertices that is maximal under planar supergraph inclusion. This removes the finite optimization step from the parent: among all planar supergraphs, choose one with maximum edge count. The route is to use finiteness of the type and of the set of simple graphs, maximize `edgeSet.ncard`, and show a strict planar supergraph would have more edges. This lemma does not assert an edge lower bound; the parent still needs the maximal planar edge theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
