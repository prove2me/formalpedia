-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
-- name    : WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:41:34.03877+00:00
-- url     : https://prove2.me/theorems/6995617f-d764-476e-bea6-5a0947b48311
-- title:
--   Finite graph edge count is bounded by unordered vertex pairs
-- statement:
--   A graph’s edge set is contained in the finite type of unordered vertex pairs, so its `ncard` is at most the number of such pairs. The parent uses this as the bound required by the maximality lemma. Prove it by showing `G.edgeSet ⊆ Set.univ` and applying the finite-set cardinality bound. This also covers empty vertex types and graphs with no edges; the remaining obligation is the set-cardinality bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
    {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by sorry
