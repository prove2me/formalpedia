-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_augmentation
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:49:49.849322+00:00
-- url     : https://prove2.me/theorems/ed4b536f-510d-4fa2-983d-546f310a24e6
-- title:
--   Maximal planar augmentation with exact edge count
-- statement:
--   Every finite graph on at least three ordered vertices with the supplied crossing-free drawing has a planar supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. The edge-inclusion inequality preserves all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_maximal_augmentation {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
