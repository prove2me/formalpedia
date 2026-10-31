-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:45:23.669696+00:00
-- url     : https://prove2.me/theorems/3966c287-bb30-4a95-bfb4-bd4f1164ddf6
-- title:
--   Connected planar extension of a drawing
-- statement:
--   Any drawable simple graph on at least three vertices has a connected drawable simple supergraph on the same vertices, with at least as many edges. The added edges can be drawn through the complement of the existing drawing to join its components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_014b5904_580f_46f1_bfdb_710877e74ec0_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G ∧ H.edgeSet.ncard ≤ G.edgeSet.ncard := by sorry
