-- Prove2me | Theorems.Thm_mme_dwz_greedy_nonhole_grouping
-- name    : mme_dwz_greedy_nonhole_grouping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:33:23.254366+00:00
-- url     : https://prove2.me/theorems/8226bfb6-9979-463c-86b0-2db82ec0b635
-- title:
--   DWZ Corollary 5.11: greedy grouping of non-hole fractions
-- statement:
--   Let η₁, ..., ηₛ in [0,1] be non-hole fractions and let L > 0. If q(L+1) ≤ sumₜ ηₜ, then the ordered list can be split into exactly q disjoint consecutive groups and an unused remainder so that every group G satisfies L ≤ sum over G < L+1. For DWZ Corollary 5.11, set L = Nℓ+1 and q = floor((sumₜ ηₜ)/(Nℓ+2)). Each group then satisfies the Hole Lemma threshold, and the strict upper bound here strengthens the corollary's non-strict bound. This theorem is only the finite grouping step; it does not assume or prove the tensor-repair conclusion of the Hole Lemma.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023: Definition 5.5 and Lemma 5.6 (printed pp. 47-49), and the greedy grouping proof of Corollary 5.11 (PDF p. 50 / printed p. 49).

import Mathlib

theorem mme_dwz_greedy_nonhole_grouping
    (weights : List ℝ)
    (h_nonneg : ∀ x ∈ weights, 0 ≤ x)
    (h_at_most_one : ∀ x ∈ weights, x ≤ 1)
    (L : ℝ) (hL : 0 < L)
    (q : ℕ) (hq : (q : ℝ) * (L + 1) ≤ weights.sum) :
    ∃ groups : List (List ℝ), ∃ remainder : List ℝ,
      weights = groups.flatten ++ remainder ∧
      groups.length = q ∧
      ∀ group ∈ groups, L ≤ group.sum ∧ group.sum < L + 1 := by sorry
