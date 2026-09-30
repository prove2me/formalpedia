-- Prove2me | solution 1 for lean_workbook_plus_62828
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:33:32.920574+00:00
-- url     : https://prove2.me/submissions/7f1878ff-4bb6-4f5d-9d05-6ed337d3ed17

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

theorem solution : ¬ (∀ n : ℕ, 0 < n → ¬ Nat.Prime (4 ^ n + n ^ 4)) := by
  intro h
  exact h 1 (by decide) (by decide)

private theorem sophie_germain_nat (x y : ℕ) :
    (x ^ 2 + 2 * y ^ 2 - 2 * x * y) *
      (x ^ 2 + 2 * y ^ 2 + 2 * x * y) = x ^ 4 + 4 * y ^ 4 := by
  have hb : 2 * x * y ≤ x ^ 2 + 2 * y ^ 2 := by
    nlinarith [two_mul_le_add_sq x y]
  zify [hb]
  ring

theorem corrected_statement (n : ℕ) (hn : 2 ≤ n) :
    ¬ Nat.Prime (4 ^ n + n ^ 4) := by
  rcases Nat.even_or_odd n with heven | hodd
  · have hd : 2 ∣ 4 ^ n + n ^ 4 :=
      dvd_add (dvd_pow (by decide : 2 ∣ 4) (by omega))
        (dvd_pow (even_iff_two_dvd.mp heven) (by decide))
    have hlarge : 4 ^ 2 ≤ 4 ^ n := pow_le_pow_right₀ (by decide) hn
    intro hp
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · omega
    · norm_num at hlarge
      omega
  · rcases hodd with ⟨k, rfl⟩
    simp only [two_mul] at hn ⊢
    have hk : 1 ≤ k := by omega
    let y : ℕ := 2 ^ k
    have hy : 2 ≤ y := by
      simpa [y] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
    have hexp : 4 ^ (k + k + 1) = 4 * y ^ 4 := by
      calc
        4 ^ (k + k + 1) = 2 ^ (2 * (k + k + 1)) := by
          rw [pow_mul]
          rfl
        _ = 2 ^ (k * 4 + 2) := by congr 1 <;> omega
        _ = 4 * y ^ 4 := by rw [pow_add, pow_mul]; dsimp [y]; ring
    have hlower :
        2 ≤ (k + k + 1) ^ 2 + 2 * y ^ 2 - 2 * (k + k + 1) * y := by
      have hsq := two_mul_le_add_sq (k + k + 1) y
      have hy2 : 4 ≤ y ^ 2 := by nlinarith
      omega
    have hupper : 2 ≤ (k + k + 1) ^ 2 + 2 * y ^ 2 +
        2 * (k + k + 1) * y := by nlinarith
    rw [hexp, Nat.add_comm, ← sophie_germain_nat (k + k + 1) y]
    exact Nat.not_prime_mul (by omega) (by omega)

#print axioms solution
#print axioms corrected_statement
