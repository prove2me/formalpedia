-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_large_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_large_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:02:35.566125+00:00
-- url     : https://prove2.me/theorems/912046a0-9a8f-4130-ac45-8f35808ce254
-- title:
--   Connected planar supergraph when the vertex set has at least three elements
-- statement:
--   For a finite linearly ordered vertex type with at least three elements, extend any graph with the specified planar drawing to a connected planar supergraph on the same vertex type, retaining all its edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_large_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
