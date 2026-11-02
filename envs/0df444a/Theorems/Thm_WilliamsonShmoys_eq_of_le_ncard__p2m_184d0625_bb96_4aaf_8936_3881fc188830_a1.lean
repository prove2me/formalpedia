-- Prove2me | Theorems.Thm_WilliamsonShmoys_eq_of_le_ncard__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
-- name    : WilliamsonShmoys.eq_of_le_ncard__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:43:14.996579+00:00
-- url     : https://prove2.me/theorems/29b047de-9085-4e84-b0be-5aad7360e9c7
-- title:
--   Equal edge counts force equality under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion together with a reverse inequality of finite edge-set cardinalities implies equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.eq_of_le_ncard__p2m_184d0625_bb96_4aaf_8936_3881fc188830_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    K = H := by sorry
