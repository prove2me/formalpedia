-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:06:40.250727+00:00
-- url     : https://prove2.me/theorems/bd5a0062-468c-43aa-a2a2-0a304df33140
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   For a nonempty finite graph with the specified planar drawing, there is a connected planar supergraph on the same vertices whose edge count is at least the original edge count. This reduces the disconnected case to the connected Euler bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 0 < Fintype.card V) : ∃ H : SimpleGraph V, K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
