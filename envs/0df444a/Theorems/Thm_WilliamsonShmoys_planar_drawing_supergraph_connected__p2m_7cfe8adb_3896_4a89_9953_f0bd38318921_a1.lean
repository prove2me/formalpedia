-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a1
-- name    : WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:33:24.322997+00:00
-- url     : https://prove2.me/theorems/304864e8-bb51-44c5-aa36-393fdd5ea875
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertices, obtained by adding edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a1 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) : ∃ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet ∧ Y.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Y := by sorry
