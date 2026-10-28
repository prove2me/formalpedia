-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_drawing_euler_face_count
-- name    : WilliamsonShmoys.planar_connected_drawing_euler_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:17:21.402069+00:00
-- url     : https://prove2.me/theorems/80977e69-15c6-40af-9893-11bf4ff92c52
-- title:
--   Euler and face-boundary count for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s equation and the lower bound on total face-boundary incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_drawing_euler_face_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hConnected : H.Connected) (hCard : 3 ≤ Fintype.card V) : ∃ F : Nat, 3 * F ≤ 2 * H.edgeSet.ncard ∧ Fintype.card V + F = H.edgeSet.ncard + 2 := by sorry
