-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:54:27.027821+00:00
-- url     : https://prove2.me/theorems/545b931b-2868-4b77-b00d-a5bf211937d5
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a connected planar supergraph on the same vertices whose edge count is at least the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
