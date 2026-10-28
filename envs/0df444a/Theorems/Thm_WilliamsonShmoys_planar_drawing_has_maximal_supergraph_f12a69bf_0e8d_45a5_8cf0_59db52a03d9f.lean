-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:36:34.821741+00:00
-- url     : https://prove2.me/theorems/5d3c61d4-9daf-4cef-b9b3-bcc6bdc9e19b
-- title:
--   Extend a drawable graph to an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under adding edges, and its edge count is at least the original graph's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
