-- Prove2me | solution 1 for lean_workbook_plus_37717
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:51:07.269743+00:00
-- url     : https://prove2.me/submissions/0849df58-9e4d-452c-90d7-89dcb3993e92

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution (a b c a1 b1 c1 a2 b2 c2 : ℕ) (hab : a ≠ a1) (hbc : b ≠ b1) (hca : c ≠ c1) (hab1 : a1 ≠ a2) (hbc1 : b1 ≠ b2) (hca1 : c1 ≠ c2) (hA: a + a1 + a2 = 9) (hB: b + b1 + b2 = 9) (hC: c + c1 + c2 = 9) : 9 ∣ (100 * a + 10 * b + c) + (100 * a1 + 10 * b1 + c1) + (100 * a2 + 10 * b2 + c2) := by
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
    | (trace "TAC:nlinarith"; (intros; nlinarith); done)
