-- Prove2me | solution 1 for lean_workbook_plus_81509
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:24:38.132722+00:00
-- url     : https://prove2.me/submissions/4837d5b0-ccd2-4bdc-9e05-32b3e591f200

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SquareFromCongruentDivisor

theorem integer_factor_criterion {a n d q : ℤ} (ha : 0 < a) (hn : a + 1 < n)
    (hd : 1 < d) (hq : 0 < q) (heq : d * q + 1 = n ^ 2 * a)
    (hmod : d ≡ 1 [ZMOD n]) : ∃ b : ℤ, 0 < b ∧ b ^ 2 = a := by
  have hn0 : 0 < n := by omega
  obtain ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hmod.symm
  have hk0 : 0 < k := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hn0.le (show k ≤ 0 by omega)
    nlinarith
  let l := n * a - k * q
  have hlq : q + 1 = n * l := by dsimp [l]; nlinarith [hk]
  have hl0 : 0 < l := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hn0.le (show l ≤ 0 by omega)
    omega
  have hrel : n * a = n * k * l + l - k := by
    have hz : n * (n * a - (n * k * l + l - k)) = 0 := by nlinarith [hk]
    have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hn0)
    omega
  have hkn : k < n := by
    by_contra h
    have hkl := mul_nonneg (show 0 ≤ n * k by positivity) (show 0 ≤ l - 1 by omega)
    have hnk := mul_nonneg (show 0 ≤ n - 1 by omega) (show 0 ≤ k - n by omega)
    have hna := mul_pos hn0 (show 0 < n - 1 - a by omega)
    nlinarith
  have hln : l < n := by
    by_contra h
    have hnl : 0 ≤ n * l - 1 := by nlinarith [mul_pos hn0 hl0]
    have hkl := mul_nonneg hnl (show 0 ≤ k - 1 by omega)
    have hnl' := mul_nonneg hn0.le (show 0 ≤ l - n by omega)
    have hna := mul_pos hn0 (show 0 < n - a by omega)
    nlinarith
  have hklmod : k ≡ l [ZMOD n] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨a - k * l, by nlinarith [hrel]⟩
  have hkl : k = l := by
    simpa only [Int.ModEq, Int.emod_eq_of_lt hk0.le hkn,
      Int.emod_eq_of_lt hl0.le hln] using hklmod
  refine ⟨k, hk0, ?_⟩
  have hz : n * (k ^ 2 - a) = 0 := by nlinarith [hrel]
  have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hn0)
  omega

theorem single_modulus_criterion {a n : ℕ} (ha : 0 < a) (hn : a + 1 < n)
    (h : ∃ d : ℕ, d ∣ n ^ 2 * a - 1 ∧ d ≠ 1 ∧ d ≡ 1 [ZMOD n]) :
    ∃ b : ℕ, b ^ 2 = a := by
  obtain ⟨d, ⟨q, hq⟩, hd, hmod⟩ := h
  have hn0 : 0 < n := by omega
  have hprod : 1 < n ^ 2 * a := by
    have := Nat.mul_le_mul_left (n ^ 2) ha
    nlinarith
  have heq : d * q + 1 = n ^ 2 * a := by omega
  have hd2 : 1 < d := by
    by_contra h
    have : d = 0 := by omega
    subst d
    simp at heq
    omega
  have hq0 : 0 < q := by
    by_contra h
    have : q = 0 := by omega
    subst q
    simp at heq
    omega
  obtain ⟨b, hb, hba⟩ := integer_factor_criterion (a := (a : ℤ)) (n := (n : ℤ))
    (d := (d : ℤ)) (q := (q : ℤ)) (by exact_mod_cast ha) (by exact_mod_cast hn)
    (by exact_mod_cast hd2) (by exact_mod_cast hq0) (by exact_mod_cast heq) hmod
  refine ⟨b.toNat, ?_⟩
  have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb.le
  exact_mod_cast (show (b.toNat : ℤ) ^ 2 = a by rw [hbcast]; exact hba)

theorem positive_moduli_iff_square {a : ℕ} (ha : 0 < a) :
    (∀ n : ℕ, 0 < n → ∃ d : ℕ,
      d ∣ n ^ 2 * a - 1 ∧ d ≠ 1 ∧ d ≡ 1 [ZMOD n]) ↔ ∃ b : ℕ, b ^ 2 = a := by
  constructor
  · intro h
    exact single_modulus_criterion ha (show a + 1 < a + 2 by omega)
      (h (a + 2) (by omega))
  · rintro ⟨b, rfl⟩ n hn
    have hb : 0 < b := by nlinarith
    have hnb : 0 < n * b := Nat.mul_pos hn hb
    refine ⟨n * b + 1, ?_, by omega, ?_⟩
    · refine ⟨n * b - 1, ?_⟩
      have ht : n * b - 1 + 1 = n * b := by omega
      have hsq : 1 ≤ n ^ 2 * b ^ 2 := by nlinarith [sq_nonneg (n * b - 1)]
      have := Nat.sub_add_cancel hsq
      nlinarith [ht]
    · apply Int.modEq_iff_dvd.mpr
      refine ⟨-(b : ℤ), ?_⟩
      push_cast
      ring

theorem single_modulus_iff_square {a n : ℕ} (ha : 0 < a) (hn : a + 1 < n) :
    (∃ d : ℕ, d ∣ n ^ 2 * a - 1 ∧ d ≠ 1 ∧ d ≡ 1 [ZMOD n]) ↔
      ∃ b : ℕ, b ^ 2 = a := by
  exact ⟨single_modulus_criterion ha hn,
    fun h => (positive_moduli_iff_square ha).mpr h n (by omega)⟩

end SquareFromCongruentDivisor

theorem solution {a : ℕ} (ha : 0 < a)
    (h : ∀ n : ℕ, ∃ d : ℕ, d ∣ n ^ 2 * a - 1 ∧ d ≠ 1 ∧ d ≡ 1 [ZMOD n]) :
    ∃ b : ℕ, b ^ 2 = a := by
  exact SquareFromCongruentDivisor.single_modulus_criterion ha
    (show a + 1 < a + 2 by omega) (h (a + 2))
