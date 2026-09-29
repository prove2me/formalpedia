-- Prove2me | solution 1 for lean_workbook_plus_70223
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:33:04.742122+00:00
-- url     : https://prove2.me/submissions/58488a64-cefa-4a1b-abf0-8b9597d14df9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution (n d : ℕ)
  (h₀ : n + d = 70)
  (h₁ : 5 * n + 10 * d = 555)
  (h₂ : 5 * n + 5 * d = 350)
  (h₃ : 5 * d = 205)
  (h₄ : d = 41)
  (h₅ : n = 29)
  (h₆ : d - n = 12) :
  d - n = 12 := by
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
