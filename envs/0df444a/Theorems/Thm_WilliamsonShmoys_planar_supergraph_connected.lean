-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_connected
-- name    : WilliamsonShmoys.planar_supergraph_connected
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T09:41:07.233549+00:00
-- url     : https://prove2.me/theorems/ff216d4b-5b3d-4d13-822a-a4421ba6f0ad
-- title:
--   Connected planar supergraph extension
-- statement:
--   Every finite graph with the supplied plane drawing has a connected planar supergraph on the same vertex type, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_connected {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
