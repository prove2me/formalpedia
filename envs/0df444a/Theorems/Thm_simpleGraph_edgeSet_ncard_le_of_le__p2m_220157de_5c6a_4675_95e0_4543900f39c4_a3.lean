-- Prove2me | Theorems.Thm_simpleGraph_edgeSet_ncard_le_of_le__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
-- name    : simpleGraph_edgeSet_ncard_le_of_le__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:23:57.490987+00:00
-- url     : https://prove2.me/theorems/0652b786-f388-427b-bca9-51e8efea4ac3
-- title:
--   Edge cardinality is monotone under edge inclusion
-- statement:
--   For finite vertex types, edge-set inclusion implies monotonicity of finite edge-set cardinalities; combine finite-set cardinality monotonicity with the given bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem simpleGraph_edgeSet_ncard_le_of_le__p2m_220157de_5c6a_4675_95e0_4543900f39c4_a3
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hEdge : G.edgeSet ⊆ H.edgeSet)
    (N : Nat)
    (hBound : H.edgeSet.ncard ≤ N) :
    G.edgeSet.ncard ≤ N := by sorry
