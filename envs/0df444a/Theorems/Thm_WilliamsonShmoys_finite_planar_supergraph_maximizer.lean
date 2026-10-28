-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximizer
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximizer
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:48:19.672636+00:00
-- url     : https://prove2.me/theorems/5b97ad24-bab5-44ba-9d9c-ef6c5c45fc3f
-- title:
--   A maximal drawable supergraph on a finite vertex type
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same finite vertex type that is maximal among drawable supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_supergraph_maximizer
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
