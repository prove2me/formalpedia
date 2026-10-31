-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:39:29.787772+00:00
-- url     : https://prove2.me/theorems/1076f7d9-8cab-4c50-ba02-63cd640503d2
-- title:
--   Edge count of an inclusion maximal drawable graph
-- statement:
--   An inclusion maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0c9ddbae_e05c_4655_8aee_21825ef9cfbc_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ¬ ∃ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn N) : 3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
