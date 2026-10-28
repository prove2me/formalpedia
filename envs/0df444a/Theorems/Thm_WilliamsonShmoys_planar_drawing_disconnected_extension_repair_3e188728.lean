-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension_repair_3e188728
-- name    : WilliamsonShmoys.planar_drawing_disconnected_extension_repair_3e188728
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:45:29.226671+00:00
-- url     : https://prove2.me/theorems/03f711f0-2425-4a76-af58-b71ede1ef56c
-- title:
--   Connect a disconnected planar drawing by adding edges
-- statement:
--   Every disconnected, nonempty finite graph with the supplied crossing-free drawing has a connected planar supergraph on the same vertices that retains all its edges and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_disconnected_extension_repair_3e188728
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ Y.Connected) :
    ∃ H : SimpleGraph V,
      Y ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
