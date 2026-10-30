-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:44.228113+00:00
-- url     : https://prove2.me/theorems/6b9ae2e6-12e7-4e83-8278-afd885802f8b
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite graph with a crossing-free drawing has an integer face count satisfying Euler's vertex-edge-face equation. This removes the topological face-count existence step from the parent. A proof route is to obtain the plane embedding's rotation system and face permutation, count its cycles as faces, and apply the Euler characteristic formula for a connected plane graph. The drawing and connectedness hypotheses are essential to that route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : ∃ f : ℤ, (Fintype.card V : ℤ) - (T.edgeSet.ncard : ℤ) + f = 2 := by sorry
