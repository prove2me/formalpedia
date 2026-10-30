-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:00:43.870963+00:00
-- url     : https://prove2.me/theorems/6b626863-f2be-4ee2-b28d-eb6793e9b57b
-- title:
--   Monotonicity of finite graph edge-set cardinality
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge-set cardinality is no larger. This routine step follows by inclusion of edge sets and monotonicity of cardinality for finite sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4 {V : Type} [Fintype V] (M N : SimpleGraph V) (hMN : M ≤ N) : M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
