-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_le_of_edgeSet_ncard_le__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
-- name    : WilliamsonShmoys.simpleGraph_eq_of_le_of_edgeSet_ncard_le__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:52:02.012131+00:00
-- url     : https://prove2.me/theorems/f9c132d2-9834-4ff1-b191-50337ff5d514
-- title:
--   An edge-set cardinality bound forces equality of finite graphs
-- statement:
--   If one finite simple graph is contained in another and the latter's edge set has no greater cardinality, the graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.simpleGraph_eq_of_le_of_edgeSet_ncard_le__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    G = H := by sorry
