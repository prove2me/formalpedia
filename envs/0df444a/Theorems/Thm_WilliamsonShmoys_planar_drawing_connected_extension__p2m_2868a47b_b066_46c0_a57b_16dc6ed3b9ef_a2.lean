-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:15:47.53734+00:00
-- url     : https://prove2.me/theorems/93892d71-84f1-4ed6-a896-c06ddcff432e
-- title:
--   Connected planar extension on the same vertices
-- statement:
--   A disconnected finite graph with a crossing-free drawing can be extended on the same vertex set to a connected simple graph with a crossing-free drawing, retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : HasPlanarDrawingOn G) (hconn : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
