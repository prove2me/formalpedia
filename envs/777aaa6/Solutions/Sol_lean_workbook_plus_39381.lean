-- Prove2me | solution 1 for lean_workbook_plus_39381
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:30:15.410098+00:00
-- url     : https://prove2.me/submissions/0abadfdc-2e6b-4eaf-997a-31df9eb13c65

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 200000 in
theorem solution (a b c r₁ r₂ r₃ r₄ r₅ r₆ : ℤ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : r₁ + r₂ = a)
  (h₂ : r₁ * r₂ = b)
  (h₃ : r₃ + r₄ = b)
  (h₄ : r₃ * r₄ = c)
  (h₅ : r₅ + r₆ = c)
  (h₆ : r₅ * r₆ = a)
  : (r₁ - 1) * (r₂ - 1) + (r₃ - 1) * (r₄ - 1) + (r₅ - 1) * (r₆ - 1) = 3 := by
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
    | (trace "TAC:nlinarith_sq"; (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]); done)
    | (trace "TAC:constructor_nlinarith"; (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]); done)
