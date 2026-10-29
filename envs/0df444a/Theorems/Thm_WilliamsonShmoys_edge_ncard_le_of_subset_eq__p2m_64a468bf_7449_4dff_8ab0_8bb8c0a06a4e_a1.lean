-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_le_of_subset_eq__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
-- name    : WilliamsonShmoys.edge_ncard_le_of_subset_eq__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:35:33.862712+00:00
-- url     : https://prove2.me/theorems/862e4f64-61ea-492f-ab3e-68ec5de0860e
-- title:
--   Edge count is monotone under edge-set inclusion
-- statement:
--   For finite simple graphs on the same vertex type, if one edge set is contained in the other and the larger edge set has size 3|V|−6, then the smaller edge set has size at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_ncard_le_of_subset_eq__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hSub : G.edgeSet ⊆ H.edgeSet)
    (hCount : H.edgeSet.ncard = 3 * Fintype.card V - 6) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
