-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_ge3_c00979a8
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_ge3_c00979a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:58:15.095138+00:00
-- url     : https://prove2.me/theorems/2bffb211-45d2-4023-91d0-8f9de52e4ceb
-- title:
--   Connect components of a planar drawing with at least three vertices
-- statement:
--   For a drawn finite simple graph with at least three vertices, extend it on the same vertices to a connected graph with a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_ge3_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
