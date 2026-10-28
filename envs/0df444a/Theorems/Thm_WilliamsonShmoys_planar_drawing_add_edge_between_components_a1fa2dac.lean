-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components_a1fa2dac
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_components_a1fa2dac
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T10:01:14.159195+00:00
-- url     : https://prove2.me/theorems/26f58981-6b7a-44cd-b025-a1a9bf3ac277
-- title:
--   Planar drawing extension joining separate components
-- statement:
--   Every disconnected graph with a planar drawing on a finite ordered vertex type has a strict planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_components_a1fa2dac
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ G ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
