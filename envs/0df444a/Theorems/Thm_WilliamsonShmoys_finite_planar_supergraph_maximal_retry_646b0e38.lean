-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal_retry_646b0e38
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximal_retry_646b0e38
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:25:34.896552+00:00
-- url     : https://prove2.me/theorems/7bbaa297-cf46-408b-bea3-69ed86205134
-- title:
--   Maximal drawable supergraph on a fixed vertex set
-- statement:
--   Every finite graph with a planar drawing has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs. Choose a graph with the largest edge count among the finitely many drawable supergraphs containing the original graph. If a drawable supergraph contains it, inclusion and maximal edge count force equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_maximal_retry_646b0e38
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
