-- Prove2me | solution 1 for lean_workbook_plus_16223
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T01:05:22.601558+00:00
-- url     : https://prove2.me/submissions/6ec53e30-4b87-45f4-b170-438a0b25a9fd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

set_option maxHeartbeats 400000 in
theorem solution (n : ℕ) (k₁ k₂ k₃ : ℕ) (x : Fin n → NNReal) : (n - 2) * (n + 1) * (∑ i, (x i) ^ (k₁ + k₂) + ∑ i, (x i) ^ (k₂ + k₃) + ∑ i, (x i) ^ (k₃ + k₁)) - 2 * (n - 2) * (∑ i, (x i) ^ k₁ * ∑ i, (x i) ^ k₂ + ∑ i, (x i) ^ k₂ * ∑ i, (x i) ^ k₃ + ∑ i, (x i) ^ k₃ * ∑ i, (x i) ^ k₁) + 3 * ∑ i, (x i) ^ (k₁ + k₂ + k₃) + 6 * (∑ i, (x i) ^ k₁) * (∑ i, (x i) ^ k₂) * (∑ i, (x i) ^ k₃) - 3 * (∑ i, (x i) ^ (k₁ + k₂)) * (∑ i, (x i) ^ k₃) - 3 * (∑ i, (x i) ^ (k₂ + k₃)) * (∑ i, (x i) ^ k₁) - 3 * (∑ i, (x i) ^ (k₃ + k₁)) * (∑ i, (x i) ^ k₂) + 3 * (n - 1) * (n - 2) ≥ 0 := by
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
