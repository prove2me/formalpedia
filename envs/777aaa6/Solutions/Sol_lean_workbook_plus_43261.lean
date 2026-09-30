-- Prove2me | solution 1 for lean_workbook_plus_43261
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:58:28.606789+00:00
-- url     : https://prove2.me/submissions/e51c2445-be5f-405f-ab81-ac65605db082

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

namespace CyclotomicPowerSumDivisibility

theorem general_divisibility (a n : ℕ) :
    a ^ 2 + a + 1 ∣ a ^ (n + 2) + (a + 1) ^ (2 * n + 1) := by
  have hbase : (a + 1) ^ 2 ≡ a [MOD a ^ 2 + a + 1] := by
    calc
      (a + 1) ^ 2 = a + (a ^ 2 + a + 1) := by ring
      _ ≡ a [MOD a ^ 2 + a + 1] := Nat.add_modEq_right
  have hpower := hbase.pow n
  have hsum : a ^ n * a ^ 2 + ((a + 1) ^ 2) ^ n * (a + 1) ≡
      a ^ n * a ^ 2 + a ^ n * (a + 1) [MOD a ^ 2 + a + 1] :=
    (hpower.mul_right (a + 1)).add_left (a ^ n * a ^ 2)
  have hleft : a ^ (n + 2) + (a + 1) ^ (2 * n + 1) =
      a ^ n * a ^ 2 + ((a + 1) ^ 2) ^ n * (a + 1) := by
    rw [pow_add, pow_add, pow_mul, pow_one]
  have hright : a ^ n * a ^ 2 + a ^ n * (a + 1) =
      (a ^ 2 + a + 1) * a ^ n := by ring
  rw [hright] at hsum
  have hzero : (a ^ 2 + a + 1) * a ^ n ≡ 0 [MOD a ^ 2 + a + 1] :=
    (show a ^ 2 + a + 1 ∣ (a ^ 2 + a + 1) * a ^ n from ⟨a ^ n, rfl⟩).modEq_zero_nat
  apply Nat.modEq_zero_iff_dvd.mp
  rw [hleft]
  exact hsum.trans hzero

theorem all_n (n : ℕ) : 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  exact general_divisibility 11 n

end CyclotomicPowerSumDivisibility

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
  exact CyclotomicPowerSumDivisibility.all_n n
