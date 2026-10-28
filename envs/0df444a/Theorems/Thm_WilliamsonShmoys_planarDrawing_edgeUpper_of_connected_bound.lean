-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper_of_connected_bound
-- name    : WilliamsonShmoys.planarDrawing_edgeUpper_of_connected_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:45:27.84265+00:00
-- url     : https://prove2.me/theorems/6460aed0-8aec-4580-ae45-dbd47c264784
-- title:
--   Reduce the planar edge bound to connected drawings
-- statement:
--   The planar edge bound for all drawings on at least three vertices follows from the connected case by adding noncrossing edges between components while preserving the vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_edgeUpper_of_connected_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (connectedBound : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (H : SimpleGraph W), H.Connected →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      3 <= Fintype.card W →
      H.edgeSet.ncard + 6 <= 3 * Fintype.card W)
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
