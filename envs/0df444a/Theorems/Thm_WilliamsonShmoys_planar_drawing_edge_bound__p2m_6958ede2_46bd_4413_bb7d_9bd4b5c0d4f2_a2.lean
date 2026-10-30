-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:29.284719+00:00
-- url     : https://prove2.me/theorems/638ff1ed-8b53-4df9-8415-0aa43fe61583
-- title:
--   Edge bound for a finite drawable simple graph
-- statement:
--   This is the standard simple planar graph edge bound in natural-number form, without requiring connectedness. It is tight for a triangle: six edges-with-multiplicity in the inequality correspond to `e + 6 = 3v` when `v = 3, e = 3`. The hypotheses `hV` and simplicity are the usual conditions for this bound. A proof route extracts a plane embedding, counts two side incidences per edge and at least three boundary incidences per face, and handles bridges through their two side incidences; alternatively, triangulate a planar completion and compare edge counts. This removes the numerical edge-bound obligation from the parent. The drawing-to-embedding and incidence or triangulation argument remain the core obligation for this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_6958ede2_46bd_4413_bb7d_9bd4b5c0d4f2_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hHplanar : HasPlanarDrawingOn H) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
