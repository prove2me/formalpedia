-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_repair_3e188728
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_repair_3e188728
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:17:51.078741+00:00
-- url     : https://prove2.me/theorems/8883c6ae-f4e9-406d-a326-4315586c1a92
-- title:
--   Connected extension of a planar drawing
-- statement:
--   Any nonempty finite graph with the supplied crossing-free drawing has a connected supergraph on the same vertices with a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_repair_3e188728
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hV : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V,
      H.Connected ∧ HasPlanarDrawingOn H ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
