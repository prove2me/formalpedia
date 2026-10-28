-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_edge_extension
-- name    : WilliamsonShmoys.planar_disconnected_edge_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T23:22:58.755505+00:00
-- url     : https://prove2.me/theorems/c74973eb-5bab-41bd-b2e4-21b80a39bfa2
-- title:
--   Extend a disconnected planar drawing by an edge
-- statement:
--   If a finite graph on an ordered vertex type has a crossing-free drawing and is disconnected, it can be extended to a graph with a crossing-free drawing and strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_edge_extension {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hDisconnected : ¬ K.Connected) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard < H.edgeSet.ncard := by sorry
