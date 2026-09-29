-- Prove2me | Theorems.Thm_mme_CW_q6_primaryHashFamily_common_balanced_half_mass
-- name    : mme_CW_q6_primaryHashFamily_common_balanced_half_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:32:50.712206+00:00
-- url     : https://prove2.me/theorems/a00da0f9-3e8e-4046-b22e-6256fe1f7d2b
-- title:
--   One coordinate half balances a polynomial fraction of a q=6 primary hash family
-- statement:
--   Let a q=6 primary hash family have $A$ outer fibers, each with $H$ entries, and coupled length $N=2n$.  Then there is one coordinate half $S$ of size $2n$ and a retained set $P$ of family entries such that every entry in $P$ has the required balanced X histogram on $S$ and balanced Y histogram on the complement, while
--
--   $$AH\leq (2n+1)^4|P|.$$
--
--   Thus one common paired halving retains at least a polynomial fraction of all primary-hash entries.  This is the exact double-counting bridge needed before uniformizing the surviving outer fibers.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_many_central_balanced_halves
import Theorems.Thm_mme_CW_q6_central_four_cell_choice_polynomial_capacity
import Theorems.Thm_mme_finset_common_witness_of_uniform_many

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_q6_primaryHashFamily_common_balanced_half_mass
    {n L G A H : ℕ} (hLG : L + G = 2 * n)
    (family : CWQ6PrimaryHashFamily (2 * n) L G A H) :
    ∃ S : Finset (Fin (2 * (2 * n))),
      ∃ P : Finset (Fin A × Fin H),
        S.card = 2 * n ∧
        (∀ p ∈ P,
          (∀ grade : Fin 3,
            (S.filter (fun j ↦ (family.entry p).1 0 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0) ∧
          (∀ grade : Fin 3,
            ((Finset.univ \ S).filter
              (fun j ↦ (family.entry p).1 1 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0)) ∧
        A * H ≤ (2 * n + 1) ^ 4 * P.card := by
  sorry
