-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connectivity_extension_e2002294_532e_4f58_bb0b_2f40f61d66b4
-- name    : WilliamsonShmoys.planar_drawing_connectivity_extension_e2002294_532e_4f58_bb0b_2f40f61d66b4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:50:45.179083+00:00
-- url     : https://prove2.me/theorems/c9444b85-a41b-41f0-a8c3-e7804df0a8ea
-- title:
--   Connect a drawable graph with at least three vertices
-- statement:
--   A finite graph on at least three vertices with a crossing-free drawing has a connected supergraph on the same vertices that also has a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_connectivity_extension_e2002294_532e_4f58_bb0b_2f40f61d66b4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ K' : SimpleGraph V, K ≤ K' ∧ K'.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧ K.edgeSet.ncard ≤ K'.edgeSet.ncard := by sorry
