-- Prove2me | solution 1 for lean_workbook_plus_8263
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:05:44.120525+00:00
-- url     : https://prove2.me/submissions/446181e4-40b0-4f70-b597-97964598f26c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 400000 in
theorem solution (n p : ℤ) : (2 * Real.sqrt (143 * n ^ 2 + 864 * n + 1081) = p ^ 2 - 24 * n - 70) ↔ (2 * Real.sqrt (143 * n ^ 2 + 864 * n + 1081) = p ^ 2 - 24 * n - 70) := by
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
    | (trace "TAC:nlinarith_sq"; (intros; nlinarith [sq_nonneg (n), sq_nonneg (p), sq_nonneg (n - p), sq_nonneg (n + p)]))
    | (trace "TAC:constructor_nlinarith"; (intros; constructor <;> nlinarith [sq_nonneg (n), sq_nonneg (p), sq_nonneg (n - p), sq_nonneg (n + p)]))
    | (trace "TAC:field_simp_nlinarith"; (intros; field_simp; nlinarith [sq_nonneg (n), sq_nonneg (p), sq_nonneg (n - p), sq_nonneg (n + p)]))
    | (trace "TAC:norm_num_nlinarith"; (intros; norm_num; nlinarith [sq_nonneg (n), sq_nonneg (p), sq_nonneg (n - p), sq_nonneg (n + p)]))
