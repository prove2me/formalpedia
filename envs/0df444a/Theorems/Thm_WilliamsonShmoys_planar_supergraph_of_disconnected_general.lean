-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_of_disconnected_general
-- name    : WilliamsonShmoys.planar_supergraph_of_disconnected_general
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T01:42:41.023989+00:00
-- url     : https://prove2.me/theorems/873df504-ff5c-4858-bd17-1b8a77bee0a8
-- title:
--   A disconnected drawable graph has a strict drawable supergraph without a size bound
-- statement:
--   Every disconnected graph with a crossing-free drawing has a strictly larger drawable supergraph on the same vertices, without a lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_of_disconnected_general
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hDisconnected : ¬ L.Connected) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ M ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
