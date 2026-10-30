-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_mono__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_count_mono__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:04:23.364985+00:00
-- url     : https://prove2.me/theorems/ee58d5c2-29d5-46ec-9d4c-cfc62de1045a
-- title:
--   Monotonicity of edge count under subgraph inclusion
-- statement:
--   For finite vertex types, subgraph inclusion implies monotonicity of the edge-set cardinality. This follows by showing the smaller graph’s edge set is included in the larger graph’s finite edge set, then applying cardinality monotonicity. It supplies the counting step from the original graph to its maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_drawing_edge_count_mono__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
    {V : Type} [Fintype V]
    (G M : SimpleGraph V)
    (hGM : G ≤ M) :
    G.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
