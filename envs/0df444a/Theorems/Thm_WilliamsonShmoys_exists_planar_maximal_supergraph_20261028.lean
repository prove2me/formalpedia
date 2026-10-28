-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_maximal_supergraph_20261028
-- name    : WilliamsonShmoys.exists_planar_maximal_supergraph_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:03:02.375311+00:00
-- url     : https://prove2.me/theorems/8bd4a703-328e-4f9b-a37a-a07e66f64b09
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that has no drawable proper supergraph. Finiteness allows choosing a drawable supergraph with the largest edge set; any proper drawable extension would contradict that choice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_maximal_supergraph_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry
