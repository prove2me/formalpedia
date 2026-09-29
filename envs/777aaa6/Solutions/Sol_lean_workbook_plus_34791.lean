-- Prove2me | solution 1 for lean_workbook_plus_34791
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:04:07.053611+00:00
-- url     : https://prove2.me/submissions/e0e2a31f-b511-48d4-a162-332eca34d258

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution (x : ℕ) (h₁ : (5 * x + 2) % 6 = 4) (h₂ : (3 * x + 4) % 6 = 4) (h₃ : (2 * x + 3) % 6 = 2) : x ≡ 1 [ZMOD 6] ∨ x ≡ 3 [ZMOD 6] ∨ x ≡ 5 [ZMOD 6] := by
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
    | (trace "TAC:mod_cases"; (intros; simp only [Int.ModEq, Nat.ModEq] at *; have hm : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega; rcases hm with h | h | h | h | h | h <;> simp [pow_two, pow_succ, Nat.mul_mod, Nat.add_mod, Nat.pow_mod, h] <;> omega); done)
    | (trace "TAC:mod_cases_decide"; (intros; simp only [Int.ModEq, Nat.ModEq] at *; have hm : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega; rcases hm with h | h | h | h | h | h <;> simp [pow_two, pow_succ, Nat.mul_mod, Nat.add_mod, Nat.pow_mod, h]); done)
    | (trace "TAC:nlinarith"; (intros; nlinarith); done)
