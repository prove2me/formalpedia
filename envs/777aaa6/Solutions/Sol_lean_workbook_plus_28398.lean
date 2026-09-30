-- Prove2me | solution 1 for lean_workbook_plus_28398
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:58.221789+00:00
-- url     : https://prove2.me/submissions/03533ba8-9e9b-4f46-bf6c-cd9fe0e8d1f3

import Mathlib.Analysis.Complex.Basic

theorem solution (m n : ℕ) (h₁ : 2 ^ m + 3 = 11 ^ n) (h₂ : 4 ≤ m) : ¬ (0 < m ∧ 0 < n) := by
  exfalso
  -- Step 1: 16 ∣ 2^m, hence 11^n ≡ 3 (mod 16), hence n ≡ 3 (mod 4).
  have h16 : 2 ^ m % 16 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
    rw [pow_add]
    simp
  have h11n16 : 11 ^ n % 16 = 3 := by omega
  have hper16 : 11 ^ n % 16 = 11 ^ (n % 4) % 16 := by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  have hn4 : n % 4 = 3 := by
    have key : ∀ s < 4, 11 ^ s % 16 = 3 → s = 3 := by decide
    exact key _ (Nat.mod_lt _ (by norm_num)) (by omega)
  -- Step 2: work modulo 65, where both 2^m and 11^n are 12-periodic.
  have hper2 : 2 ^ m % 65 = 2 ^ (m % 12) % 65 := by
    conv_lhs => rw [← Nat.div_add_mod m 12, pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  have hper11 : 11 ^ n % 65 = 11 ^ (n % 12) % 65 := by
    conv_lhs => rw [← Nat.div_add_mod n 12, pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  have key : ∀ r < 12, ∀ s < 12, s % 4 = 3 → (2 ^ r % 65 + 3) % 65 ≠ 11 ^ s % 65 := by decide
  exact key (m % 12) (Nat.mod_lt _ (by norm_num)) (n % 12) (Nat.mod_lt _ (by norm_num))
    (by omega) (by omega)
