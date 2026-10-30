-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_fda861fd_855b_4561_971f_8551142822a0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:24.205351+00:00
-- url     : https://prove2.me/theorems/072ec50e-4726-4a42-9f13-0704f4f63ce2
-- title:
--   Edge cardinality is monotone under inclusion
-- statement:
--   Inclusion of finite graph edge sets implies the same inequality for their cardinalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_fda861fd_855b_4561_971f_8551142822a0_a2 {V : Type} [Fintype V] [LinearOrder V] (P Q : SimpleGraph V) (hPQ : P.edgeSet ⊆ Q.edgeSet) : P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
