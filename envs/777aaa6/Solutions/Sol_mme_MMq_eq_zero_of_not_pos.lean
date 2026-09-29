-- Prove2me | solution 1 for mme_MMq_eq_zero_of_not_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:34.107493+00:00
-- url     : https://prove2.me/submissions/e8bbbc25-481f-4de7-9bcb-52aae9c0a5a2

import Definitions.Def_mme_tensor_bridge

/-! # Solution: zero-dimension vanishing of `MMq`.

Thin re-export of `MME.MMq_eq_zero_of_not_pos` from `Def_mme_tensor_bridge`. -/

open MME

universe u

theorem solution {K : Type u} [Field K] {n m p : ℕ}
    (h : ¬ (1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ p)) :
    MMq K n m p = 0 :=
  MME.MMq_eq_zero_of_not_pos h
