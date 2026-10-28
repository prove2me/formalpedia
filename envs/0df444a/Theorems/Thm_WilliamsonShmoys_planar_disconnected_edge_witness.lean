-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_edge_witness
-- name    : WilliamsonShmoys.planar_disconnected_edge_witness
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-25T23:51:42.767667+00:00
-- url     : https://prove2.me/theorems/0bceff89-6b0b-4b54-9d0d-49801f7da5c4
-- title:
--   Planar augmentation with an explicit new edge
-- statement:
--   Every disconnected finite graph with the specified planar drawing has a planar supergraph on the same vertices containing an edge that was absent from the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_edge_witness
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ H.Adj u v ∧ K.Adj u v := by
  sorry
