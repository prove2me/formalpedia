-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_7842deb4_e63b_4553_baf8_30586367a025
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_7842deb4_e63b_4553_baf8_30586367a025
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:16:40.989039+00:00
-- url     : https://prove2.me/theorems/57411eea-a721-40ca-9478-14ce3c8d705d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_7842deb4_e63b_4553_baf8_30586367a025 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T ≤ S) : 3 * Fintype.card V = S.edgeSet.ncard + 6 := by sorry
