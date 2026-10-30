-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
-- name    : WilliamsonShmoys.planar_edge_count_completion_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:57:56.730977+00:00
-- url     : https://prove2.me/theorems/3179f37e-52aa-4ff6-9aa1-854963e13cc0
-- title:
--   Drawable planar edge-count completion on the same vertex set
-- statement:
--   Any drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_completion_same_vertex_set_7842deb4_e63b_4553_baf8_30586367a025 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) (hCard : 3 ≤ Fintype.card V) : ∃ S : SimpleGraph V, R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧ 3 * Fintype.card V = S.edgeSet.ncard + 6 := by sorry
