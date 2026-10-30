-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:39.666886+00:00
-- url     : https://prove2.me/theorems/753165d9-816f-40a5-87b6-d0f029d10968
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   If H is a subgraph of K on the same finite vertex type, then H’s finite edge-set cardinality is at most K’s, by inclusion of their edge sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
