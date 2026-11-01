-- Prove2me | Theorems.Thm_WilliamsonShmoys_finset_subset_of_le_card_eq__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
-- name    : WilliamsonShmoys.finset_subset_of_le_card_eq__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:16.021794+00:00
-- url     : https://prove2.me/theorems/2ccd04df-4437-4c53-8d7c-a44803aa8cee
-- title:
--   A finite subset with at least as many elements is equal
-- statement:
--   If one finite set is contained in another and has at least as many elements, the two sets are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finset_subset_of_le_card_eq__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
    {α : Type} [DecidableEq α] (s t : Finset α)
    (hst : s ⊆ t) (hcard : t.card ≤ s.card) : s = t := by sorry
