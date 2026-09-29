-- Prove2me | solution 1 for lean_workbook_plus_6187
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:05:45.224451+00:00
-- url     : https://prove2.me/submissions/abbf7263-82f2-441c-9602-1cd5666dae1a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 400000 in
theorem solution (x y : ℤ) (h : ∃ k : ℤ, (x^2 - 1) / (y + 1) + (y^2 - 1) / (x + 1) = k) :
    ∃ k₁ k₂ : ℤ, (x^2 - 1) / (y + 1) = k₁ ∧ (y^2 - 1) / (x + 1) = k₂ := by
  first
    | (trace "TAC:norm_num"; norm_num)
    | (trace "TAC:decide"; decide)
    | (trace "TAC:rfl"; rfl)
    | (trace "TAC:simp"; simp)
    | (trace "TAC:norm_num_intros"; (intros; norm_num))
    | (trace "TAC:simp_intros"; (intros; simp))
    | (trace "TAC:simp_all"; (intros; simp_all))
    | (trace "TAC:positivity"; (intros; positivity))
    | (trace "TAC:omega"; (intros; omega))
    | (trace "TAC:linarith"; (intros; linarith))
    | (trace "TAC:ring"; (intros; ring))
    | (trace "TAC:field_simp_ring"; (intros; field_simp; ring))
    | (trace "TAC:norm_num_factorial"; (intros; norm_num [Nat.factorial, Nat.choose]))
    | (trace "TAC:norm_num_mod"; (intros; norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Int.emod_emod_of_dvd]))
    | (trace "TAC:constructor_norm_num"; (intros; constructor <;> norm_num))
    | (trace "TAC:norm_num_ring_nf"; (intros; norm_num; ring_nf))
    | (trace "TAC:simp_ring"; (intros; simp; ring))
    | (trace "TAC:decide_intros"; (intros; decide))
    | (trace "TAC:nlinarith_sq"; (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)]))
    | (trace "TAC:constructor_nlinarith"; (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)]))
    | (trace "TAC:field_simp_nlinarith"; (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)]))
    | (trace "TAC:norm_num_nlinarith"; (intros; norm_num; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)]))
