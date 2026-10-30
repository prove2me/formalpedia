-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- name    : WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:58.512863+00:00
-- url     : https://prove2.me/theorems/dcc97baf-a894-4b16-bd8b-dee1a77b56f8
-- title:
--   Subgraph edge count monotonicity
-- statement:
--   For finite simple graphs on the same vertex type, subgraph inclusion implies that the subgraph’s edge-set cardinality is no larger. Prove this from edge-set inclusion and monotonicity of finite set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
    {V : Type} [Fintype V]
    (K H : SimpleGraph V)
    (hKH : K ≤ H) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
