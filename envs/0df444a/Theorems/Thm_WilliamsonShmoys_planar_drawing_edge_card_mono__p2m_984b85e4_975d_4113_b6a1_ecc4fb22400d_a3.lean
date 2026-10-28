-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_card_mono__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_card_mono__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:32:37.91183+00:00
-- url     : https://prove2.me/theorems/777f9ce6-aaa0-476f-a412-93ab05cab06b
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   For finite vertex types, inclusion of simple graphs implies that the smaller graph has no more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_card_mono__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
    {V : Type} [Fintype V]
    (S T : SimpleGraph V)
    (hST : S ≤ T) :
    S.edgeSet.ncard ≤ T.edgeSet.ncard := by sorry
