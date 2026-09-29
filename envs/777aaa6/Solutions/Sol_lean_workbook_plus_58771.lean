-- Prove2me | solution 1 for lean_workbook_plus_58771
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T00:57:04.995391+00:00
-- url     : https://prove2.me/submissions/570b08f3-c46e-46f7-aaa6-735304e4d665

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 400000 in
theorem solution (a b : ℕ → ℕ) (h₁ : a 1 ≥ a 2 ∧ a 2 ≥ a 3) (h₂ : b 1 ≥ b 2 ∧ b 2 ≥ b 3) : a 1 * b 1 + a 2 * b 2 + a 3 * b 3 ≥ 1 / 3 * (a 1 + a 2 + a 3) * (b 1 + b 2 + b 3) := by
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
    | (trace "TAC:nlinarith"; (intros; nlinarith))
