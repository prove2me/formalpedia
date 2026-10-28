-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_supergraph
-- name    : WilliamsonShmoys.planar_extension_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:57:56.420798+00:00
-- url     : https://prove2.me/theorems/18bde782-847e-438f-96b7-cc5ed2ba2f1b
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Choose a planar supergraph containing the given graph that is maximal among planar supergraphs on the same vertex type. The vertex bound is retained to match the parent. A proof route is to maximize `edgeSet.ncard` over the finite collection of planar supergraphs containing `L`; any planar supergraph containing the maximizer must then have no additional edges. This isolates the finite maximization step from the topological edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_extension_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V,
          T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T := by sorry
