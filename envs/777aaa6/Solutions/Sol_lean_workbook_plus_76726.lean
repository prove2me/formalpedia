-- Prove2me | solution 1 for lean_workbook_plus_76726
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T00:56:54.141291+00:00
-- url     : https://prove2.me/submissions/ee45e739-fb5a-4ad1-aa8c-f6cde281c515

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 400000 in
theorem solution (x : ℕ → ℂ) : (∃ x1 x2 x3 x4 :ℂ, x1 + x2 * x3 * x4 = 2 ∧ x2 + x3 * x4 * x1 = 2 ∧ x3 + x4 * x1 * x2 = 2 ∧ x4 + x1 * x2 * x3 = 2) ↔ (∃ x1 x2 x3 x4 :ℂ, x1 + x2 * x3 * x4 = 2 ∧ x2 + x3 * x4 * x1 = 2 ∧ x3 + x4 * x1 * x2 = 2 ∧ x4 + x1 * x2 * x3 = 2) := by
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
