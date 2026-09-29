-- Prove2me | Theorems.Thm_mme_CW_q6_exact_address_central_cell_union_balanced
-- name    : mme_CW_q6_exact_address_central_cell_union_balanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:13:14.879138+00:00
-- url     : https://prove2.me/theorems/efa0620b-b931-46d2-bcb3-0b1143223464
-- title:
--   Central choices in the four joint cells form a balanced paired half
-- statement:
--   Let an exact coupled q=6 address have joint $XY$ cell sizes $(L,L,G,G)$, with $L+G=2n$. Choose $\lfloor L/2\rfloor$ positions from each diagonal cell 00 and 11, and $n-\lfloor L/2\rfloor$ positions from each off-diagonal cell 01 and 10. Their union has size $2n$. On this union the X word contains exactly $n$ zeros and $n$ ones, and on its complement the Y word also contains exactly $n$ zeros and $n$ ones; grade two occurs zero times.
--
--   Thus every such central four-cell choice is a valid balanced coordinate half. This is the local combinatorial input for counting many possible halves per retained primary-hash entry.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, paired 121/211 analysis in Section 7; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_joint_xy_counts

open MME

set_option autoImplicit false

theorem mme_CW_q6_exact_address_central_cell_union_balanced
    {n L G : ℕ} (hLG : L + G = 2 * n)
    (address : CWQ6ExactCoupledAddress (2 * n) L G)
    (S00 S11 S01 S10 : Finset (Fin (2 * (2 * n))))
    (h00 : S00 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 0 ∧ address.1 1 j = 0)))
    (h11 : S11 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 1 ∧ address.1 1 j = 1)))
    (h01 : S01 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 0 ∧ address.1 1 j = 1)))
    (h10 : S10 ⊆ (Finset.univ.filter
      (fun j ↦ address.1 0 j = 1 ∧ address.1 1 j = 0)))
    (hc00 : S00.card = L / 2) (hc11 : S11.card = L / 2)
    (hc01 : S01.card = n - L / 2) (hc10 : S10.card = n - L / 2) :
    let S := S00 ∪ S11 ∪ S01 ∪ S10
    S.card = 2 * n ∧
      (∀ grade : Fin 3,
        (S.filter (fun j ↦ address.1 0 j = grade)).card =
          if grade = 0 then n else if grade = 1 then n else 0) ∧
      (∀ grade : Fin 3,
        ((Finset.univ \ S).filter
          (fun j ↦ address.1 1 j = grade)).card =
          if grade = 0 then n else if grade = 1 then n else 0) := by
  sorry
