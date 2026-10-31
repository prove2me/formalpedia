-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:44.298166+00:00
-- url     : https://prove2.me/theorems/f77a0d45-43a8-40d9-8832-a602ad29dbe5
-- title:
--   Edge-set cardinality is monotone under graph inclusion
-- statement:
--   For finite vertex types, inclusion of simple graphs implies monotonicity of the cardinality of their edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1 {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
