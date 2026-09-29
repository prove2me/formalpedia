-- Prove2me | solution 1 for lean_workbook_plus_60758
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:21:20.954496+00:00
-- url     : https://prove2.me/submissions/16920db0-21e8-4d7d-b1f7-4cbdb982438e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution (n x y k : ℤ) : n + x = k^2 ∧ n + y = (k + 1)^2 → x = k^2 - n ∧ y = (k + 1)^2 - n := by
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
    | (trace "TAC:nlinarith_sq"; (intros; nlinarith [sq_nonneg (n), sq_nonneg (x), sq_nonneg (y), sq_nonneg (k), sq_nonneg (n - x), sq_nonneg (n - y), sq_nonneg (n - k), sq_nonneg (x - y), sq_nonneg (x - k), sq_nonneg (y - k), sq_nonneg (n + x), sq_nonneg (n + y), sq_nonneg (n + k), sq_nonneg (x + y), sq_nonneg (x + k), sq_nonneg (y + k)]); done)
    | (trace "TAC:constructor_nlinarith"; (intros; constructor <;> nlinarith [sq_nonneg (n), sq_nonneg (x), sq_nonneg (y), sq_nonneg (k), sq_nonneg (n - x), sq_nonneg (n - y), sq_nonneg (n - k), sq_nonneg (x - y), sq_nonneg (x - k), sq_nonneg (y - k), sq_nonneg (n + x), sq_nonneg (n + y), sq_nonneg (n + k), sq_nonneg (x + y), sq_nonneg (x + k), sq_nonneg (y + k)]); done)
