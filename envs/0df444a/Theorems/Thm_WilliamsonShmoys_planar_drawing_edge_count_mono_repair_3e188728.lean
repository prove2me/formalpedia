-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_mono_repair_3e188728
-- name    : WilliamsonShmoys.planar_drawing_edge_count_mono_repair_3e188728
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:28:12.766985+00:00
-- url     : https://prove2.me/theorems/3106a5fd-e7cd-4315-9adf-7b70efd9f0e7
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs, inclusion of graphs gives inclusion of finite edge sets, and therefore the edge-set cardinality is monotone.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_drawing_edge_count_mono_repair_3e188728
    {V : Type} [Fintype V] [LinearOrder V]
    (Y H : SimpleGraph V)
    (hYH : Y ≤ H) :
    Y.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
