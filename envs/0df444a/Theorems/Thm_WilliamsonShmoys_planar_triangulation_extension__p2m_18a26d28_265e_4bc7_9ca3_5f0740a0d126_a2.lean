-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:12.58718+00:00
-- url     : https://prove2.me/theorems/444bbc12-374a-443e-a15d-6bd6256fef03
-- title:
--   Triangulated planar extension on the same vertices
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing extends, on the same vertices, to a triangulated planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hconn : X.Connected) (hV : 3 ≤ Fintype.card V) : ∃ Y : SimpleGraph V, X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧ Y.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
