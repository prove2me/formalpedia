-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- name    : WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:03.744897+00:00
-- url     : https://prove2.me/theorems/10723389-5561-4ece-b37c-0575b86b1c20
-- title:
--   Simple graph edge count is monotone
-- statement:
--   This elementary reusable step turns graph inclusion into edge-count monotonicity. It follows by monotonicity of the edge sets and cardinality of finite sets; it keeps the parent derivation independent of details of the graph edge-set representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1 {V : Type} [Fintype V] (G K : SimpleGraph V) (hGK : G ≤ K) : G.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
