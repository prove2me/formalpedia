-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_spanning_supergraph
-- name    : WilliamsonShmoys.planar_connected_spanning_supergraph
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T00:42:51.26721+00:00
-- url     : https://prove2.me/theorems/1377c925-44a4-4fda-aa8d-348a9bd2f4fc
-- title:
--   Connected planar spanning supergraph
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_spanning_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
