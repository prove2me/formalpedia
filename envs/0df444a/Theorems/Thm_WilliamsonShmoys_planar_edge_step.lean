-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_step
-- name    : WilliamsonShmoys.planar_edge_step
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:47:42.102976+00:00
-- url     : https://prove2.me/theorems/ff44cd39-699f-466f-9c05-c6c71a53ea89
-- title:
--   Add a drawable edge between components
-- statement:
--   Every disconnected finite drawable graph has a drawable supergraph in which some pair of formerly unreachable vertices becomes reachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_step
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Reachable u v := by sorry
