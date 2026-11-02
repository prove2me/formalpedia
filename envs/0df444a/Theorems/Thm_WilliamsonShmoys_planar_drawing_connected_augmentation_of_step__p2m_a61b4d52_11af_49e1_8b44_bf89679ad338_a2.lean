-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_of_step__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_of_step__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:03:39.880301+00:00
-- url     : https://prove2.me/theorems/4a43e10e-e159-4055-9c95-47bb90addfd4
-- title:
--   Finite termination of strict planar extensions
-- statement:
--   If every disconnected planar supergraph of a finite graph has a strictly larger planar supergraph on the same vertices, then a connected planar supergraph containing the original graph exists.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_of_step__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hstep : ∀ G : SimpleGraph V, L ≤ G → HasPlanarDrawingOn G → ¬ G.Connected → ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H) : ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
