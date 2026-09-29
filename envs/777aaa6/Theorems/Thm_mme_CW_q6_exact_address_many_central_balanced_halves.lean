-- Prove2me | Theorems.Thm_mme_CW_q6_exact_address_many_central_balanced_halves
-- name    : mme_CW_q6_exact_address_many_central_balanced_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:20:03.411746+00:00
-- url     : https://prove2.me/theorems/a6e2b275-61ec-426a-ae44-c74849b595ba
-- title:
--   Every exact q=6 address has the full product family of central balanced halves
-- statement:
--   For an exact coupled q=6 address of length $2N=4n$, suppose the four joint X/Y cells have cardinalities $(L,L,G,G)$ with $L+G=2n$.  There is a finite family of balanced coordinate halves whose cardinality is exactly
--
--   $$\binom{L}{\lfloor L/2\rfloor}^2\binom{G}{n-\lfloor L/2\rfloor}^2.$$
--
--   Each half has $2n$ positions.  The X word contains exactly $n$ zeros and $n$ ones on the half, while the Y word contains exactly $n$ zeros and $n$ ones on its complement.  This exact count is the incidence input for selecting one coordinate halving shared by a large retained subfamily.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_central_cell_union_balanced
import Theorems.Thm_mme_CW_q6_exact_address_joint_xy_counts

open MME

set_option autoImplicit false

theorem mme_CW_q6_exact_address_many_central_balanced_halves
    {n L G : ℕ} (hLG : L + G = 2 * n)
    (address : CWQ6ExactCoupledAddress (2 * n) L G) :
    ∃ halves : Finset (Finset (Fin (2 * (2 * n)))),
      halves.card =
        (Nat.choose L (L / 2) * Nat.choose L (L / 2)) *
          (Nat.choose G (n - L / 2) * Nat.choose G (n - L / 2)) ∧
      ∀ S ∈ halves,
        S.card = 2 * n ∧
          (∀ grade : Fin 3,
            (S.filter (fun j ↦ address.1 0 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0) ∧
          (∀ grade : Fin 3,
            ((Finset.univ \ S).filter
              (fun j ↦ address.1 1 j = grade)).card =
              if grade = 0 then n else if grade = 1 then n else 0) := by
  sorry
