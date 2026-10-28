-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_edge_maximal
-- name    : WilliamsonShmoys.planar_extension_to_edge_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:51:28.010111+00:00
-- url     : https://prove2.me/theorems/b0c7a6d4-5e96-4b1a-96e4-a70dde01368f
-- title:
--   Extend a connected planar drawing to an edge-maximal planar graph
-- statement:
--   Every connected graph with a drawing of the specified kind has a connected, edge-maximal planar supergraph on the same finite vertex type. The extension does not decrease the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_extension_to_edge_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      (∀ G : SimpleGraph V,
        H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) := by sorry
