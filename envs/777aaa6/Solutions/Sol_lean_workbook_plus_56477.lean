-- Prove2me | solution 1 for lean_workbook_plus_56477
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:29:52.963097+00:00
-- url     : https://prove2.me/submissions/7ef43538-32e3-491d-b91d-43e685637bf3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution (a b c m n p : ℤ) : m = a + 2 * b + c ∧ n = a + b + 2 * c ∧ p = a + b + 3 * c ↔ a = 5 * n - 3 * p - m ∧ b = m + p - 2 * n ∧ c = p - n := by
  first
    | (trace "TAC:norm_num"; norm_num; done)
    | (trace "TAC:decide"; decide; done)
    | (trace "TAC:rfl"; rfl; done)
    | (trace "TAC:simp"; simp; done)
    | (trace "TAC:norm_num_intros"; (intros; norm_num); done)
    | (trace "TAC:simp_intros"; (intros; simp); done)
    | (trace "TAC:simp_all"; (intros; simp_all); done)
    | (trace "TAC:positivity"; (intros; positivity); done)
    | (trace "TAC:omega"; (intros; omega); done)
    | (trace "TAC:linarith"; (intros; linarith); done)
    | (trace "TAC:ring"; (intros; ring); done)
    | (trace "TAC:field_simp_ring"; (intros; field_simp; ring); done)
    | (trace "TAC:norm_num_factorial"; (intros; norm_num [Nat.factorial, Nat.choose]); done)
    | (trace "TAC:norm_num_mod"; (intros; norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Int.emod_emod_of_dvd]); done)
    | (trace "TAC:constructor_norm_num"; (intros; constructor <;> norm_num); done)
    | (trace "TAC:norm_num_ring_nf"; (intros; norm_num; ring_nf); done)
    | (trace "TAC:simp_ring"; (intros; simp; ring); done)
    | (trace "TAC:decide_intros"; (intros; decide); done)
    | (trace "TAC:exists_self"; (intros; exact ⟨_, fun _ => rfl⟩); done)
    | (trace "TAC:modeq_cases"; (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega); done)
    | (trace "TAC:sub_dvd_pow"; (intros; exact sub_dvd_pow_sub_pow _ _ _); done)
    | (trace "TAC:nlinarith_sq"; (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (m), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - m), sq_nonneg (b - c), sq_nonneg (b - m), sq_nonneg (c - m), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + m), sq_nonneg (b + c), sq_nonneg (b + m), sq_nonneg (c + m)]); done)
    | (trace "TAC:constructor_nlinarith"; (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (m), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - m), sq_nonneg (b - c), sq_nonneg (b - m), sq_nonneg (c - m), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + m), sq_nonneg (b + c), sq_nonneg (b + m), sq_nonneg (c + m)]); done)
