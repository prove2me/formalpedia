-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a2
-- name    : WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:26.865147+00:00
-- url     : https://prove2.me/theorems/5d42d59b-764a-4bdb-bbf1-38662a777b69
-- title:
--   Connect a planar drawing with at least three vertices by adding edges
-- statement:
--   A finite graph with a crossing-free drawing and at least three vertices has a connected planar supergraph on the same vertices, obtained by adding edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_connected__p2m_7cfe8adb_3896_4a89_9953_f0bd38318921_a2 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : ∃ Y : SimpleGraph V, X.edgeSet ⊆ Y.edgeSet ∧ Y.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Y := by sorry
