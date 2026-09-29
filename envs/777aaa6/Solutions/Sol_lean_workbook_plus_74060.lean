-- Prove2me | solution 1 for lean_workbook_plus_74060
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:21:03.049363+00:00
-- url     : https://prove2.me/submissions/42b6e5d5-d7fc-4640-aec7-d0541f656408

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution : ∀ x : ℤ, x ≡ 1 [ZMOD 12] ∨ x ≡ 3 [ZMOD 12] → x ≡ 0 [ZMOD 3] ∨ x ≡ 1 [ZMOD 3] := by
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
    | (trace "TAC:mod_cases"; (intros; simp only [Int.ModEq, Nat.ModEq] at *; have hm : x % 12 = 0 ∨ x % 12 = 1 ∨ x % 12 = 2 ∨ x % 12 = 3 ∨ x % 12 = 4 ∨ x % 12 = 5 ∨ x % 12 = 6 ∨ x % 12 = 7 ∨ x % 12 = 8 ∨ x % 12 = 9 ∨ x % 12 = 10 ∨ x % 12 = 11 := by omega; rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [pow_two, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod, Int.emod_emod_of_dvd, h] <;> omega); done)
    | (trace "TAC:mod_cases_decide"; (intros; simp only [Int.ModEq, Nat.ModEq] at *; have hm : x % 12 = 0 ∨ x % 12 = 1 ∨ x % 12 = 2 ∨ x % 12 = 3 ∨ x % 12 = 4 ∨ x % 12 = 5 ∨ x % 12 = 6 ∨ x % 12 = 7 ∨ x % 12 = 8 ∨ x % 12 = 9 ∨ x % 12 = 10 ∨ x % 12 = 11 := by omega; rcases hm with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [pow_two, pow_succ, Int.mul_emod, Int.add_emod, Int.sub_emod, Int.emod_emod_of_dvd, h]); done)
    | (trace "TAC:nlinarith_sq"; (intros; nlinarith [sq_nonneg (x)]); done)
