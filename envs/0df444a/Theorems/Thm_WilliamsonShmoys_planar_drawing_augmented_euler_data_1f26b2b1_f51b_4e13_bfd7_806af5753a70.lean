-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmented_euler_data_1f26b2b1_f51b_4e13_bfd7_806af5753a70
-- name    : WilliamsonShmoys.planar_drawing_augmented_euler_data_1f26b2b1_f51b_4e13_bfd7_806af5753a70
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:34:12.804157+00:00
-- url     : https://prove2.me/theorems/e835467c-535b-4b1b-93f3-615a03827815
-- title:
--   Augmented Euler data for a planar drawing
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing, there are augmented edge and face counts satisfying the original-edge inclusion bound, Euler’s formula, and the face-boundary incidence inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmented_euler_data_1f26b2b1_f51b_4e13_bfd7_806af5753a70 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ M f : ℕ, K.edgeSet.ncard ≤ M ∧ Fintype.card V + f = M + 2 ∧ 3 * f ≤ 2 * M := by sorry
