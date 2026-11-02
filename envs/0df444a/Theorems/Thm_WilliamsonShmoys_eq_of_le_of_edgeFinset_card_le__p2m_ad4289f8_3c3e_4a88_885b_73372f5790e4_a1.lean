-- Prove2me | Theorems.Thm_WilliamsonShmoys_eq_of_le_of_edgeFinset_card_le__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
-- name    : WilliamsonShmoys.eq_of_le_of_edgeFinset_card_le__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:04:09.737201+00:00
-- url     : https://prove2.me/theorems/f0c2703d-71de-4813-af11-c52d52f8debe
-- title:
--   Inclusion and reverse edge-count bound imply equality
-- statement:
--   For finite graphs on the same vertex type, if `M` is a subgraph of `N` and `N` has no more edges than `M`, then `N = M`. The parent obtains the edge-count inequality from the first child. Prove this independently by showing the edge finset of `M` is included in that of `N`; finite-set cardinality monotonicity then forces the edge finsets to agree, which yields equality of the simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.eq_of_le_of_edgeFinset_card_le__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    M ≤ N → N.edgeFinset.card ≤ M.edgeFinset.card → N = M := by sorry
