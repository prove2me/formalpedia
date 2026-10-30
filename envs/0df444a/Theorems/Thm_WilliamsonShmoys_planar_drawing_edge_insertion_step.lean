-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_insertion_step
-- name    : WilliamsonShmoys.planar_drawing_edge_insertion_step
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T17:24:40.185861+00:00
-- url     : https://prove2.me/theorems/4ec347cd-4c63-45be-9341-157dae494809
-- title:
--   Insert an edge into a disconnected planar drawing
-- statement:
--   Every disconnected finite graph with a drawing as specified by HasPlanarDrawingOn admits a strictly larger planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_insertion_step {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hnc : ¬ L.Connected) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ L.edgeSet.ncard < M.edgeSet.ncard := by sorry
