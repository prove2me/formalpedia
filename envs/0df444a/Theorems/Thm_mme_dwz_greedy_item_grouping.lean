-- Prove2me | Theorems.Thm_mme_dwz_greedy_item_grouping
-- name    : mme_dwz_greedy_item_grouping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:32:21.426951+00:00
-- url     : https://prove2.me/theorems/64b6007f-8530-4281-9b28-59135079af0f
-- title:
--   DWZ greedy aggregate grouping retains the broken-copy items
-- statement:
--   Let a finite ordered family of items carry weights in $[0,1]$. If its total weight is at least $q(L+1)$, then a literal prefix can be divided into exactly $q$ consecutive groups, each having weight at least $L$ and less than $L+1$; the unused items form a remainder. Unlike the earlier scalar-only grouping lemma, this version retains the actual items and the exact prefix decomposition, which is needed to regroup a tensor direct sum without cloning summands.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Corollary 5.11 and its greedy grouping argument; https://arxiv.org/abs/2210.10173

import Mathlib

set_option autoImplicit false

theorem mme_dwz_greedy_item_grouping
    {Item : Type} (weight : Item → ℝ)
    (items : List Item)
    (h_nonneg : ∀ x ∈ items, 0 ≤ weight x)
    (h_at_most_one : ∀ x ∈ items, weight x ≤ 1)
    (L : ℝ) (hL : 0 < L)
    (q : ℕ) (hq : (q : ℝ) * (L + 1) ≤ (items.map weight).sum) :
    ∃ groups : List (List Item), ∃ remainder : List Item,
      items = groups.flatten ++ remainder ∧
      groups.length = q ∧
      ∀ group ∈ groups,
        L ≤ (group.map weight).sum ∧
          (group.map weight).sum < L + 1 := by
  sorry
