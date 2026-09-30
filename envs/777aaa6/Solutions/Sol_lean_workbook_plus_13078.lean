-- Prove2me | solution 1 for lean_workbook_plus_13078
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:14:23.019953+00:00
-- url     : https://prove2.me/submissions/b6b5df0e-e1d0-464e-9903-232bd51b6274

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

private theorem quadratic_congruence (n : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, 4 * a ^ 2 + 9 * b ^ 2 ≡ 1 [MOD n] := by
  let t := ordProj[2] n
  let o := ordCompl[2] n
  have hprod : t * o = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have h2o : Nat.Coprime 2 o := Nat.coprime_ordCompl (by decide) hn.ne'
  have hto : Nat.Coprime t o := h2o.pow_left _
  have h2to : Nat.Coprime (2 * t) o := h2o.mul_left hto
  have ht3 : Nat.Coprime t 3 := (show Nat.Coprime 2 3 by decide).pow_left _
  have ht3o : Nat.Coprime t (3 * o) := ht3.mul_right hto
  let x := Nat.chineseRemainder h2to 0 1
  let y := Nat.chineseRemainder ht3o 1 0
  have hx2 : 2 ∣ x.val := Nat.modEq_zero_iff_dvd.mp
    (x.property.1.of_dvd (dvd_mul_right 2 t))
  have hy3 : 3 ∣ y.val := Nat.modEq_zero_iff_dvd.mp
    (y.property.2.of_dvd (dvd_mul_right 3 o))
  have hxt : x.val ≡ 0 [MOD t] :=
    x.property.1.of_dvd (dvd_mul_left t 2)
  have hyo : y.val ≡ 0 [MOD o] :=
    y.property.2.of_dvd (dvd_mul_left o 3)
  have hsumt : x.val ^ 2 + y.val ^ 2 ≡ 1 [MOD t] := by
    simpa using (hxt.pow 2).add (y.property.1.pow 2)
  have hsumo : x.val ^ 2 + y.val ^ 2 ≡ 1 [MOD o] := by
    simpa using (x.property.2.pow 2).add (hyo.pow 2)
  have hsum : x.val ^ 2 + y.val ^ 2 ≡ 1 [MOD n] := by
    rw [← hprod]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hto).mp ⟨hsumt, hsumo⟩
  refine ⟨x.val / 2, y.val / 3, ?_⟩
  convert hsum using 1
  have hx := Nat.mul_div_cancel' hx2
  have hy := Nat.mul_div_cancel' hy3
  nlinarith

theorem arbitrarily_large_quadratic_witnesses (n M : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, M < a ∧ M < b ∧ n ∣ 4 * a ^ 2 + 9 * b ^ 2 - 1 := by
  obtain ⟨a, b, hab⟩ := quadratic_congruence n hn
  let A := a + n * (M + 1)
  let B := b + n * (M + 1)
  have hA : M < A := by dsimp [A]; nlinarith
  have hB : M < B := by dsimp [B]; nlinarith
  have hAm : A ≡ a [MOD n] := Nat.add_modulus_mul_modEq_iff.mpr rfl
  have hBm : B ≡ b [MOD n] := Nat.add_modulus_mul_modEq_iff.mpr rfl
  have hcong : 4 * A ^ 2 + 9 * B ^ 2 ≡ 1 [MOD n] :=
    (((hAm.pow 2).mul_left 4).add ((hBm.pow 2).mul_left 9)).trans hab
  refine ⟨A, B, hA, hB, (Nat.modEq_iff_dvd' ?_).mp hcong.symm⟩
  nlinarith

theorem solution (n : ℕ) : ∃ a b : ℕ, n ∣ 4 * a ^ 2 + 9 * b ^ 2 - 1 := by
  by_cases hn : n = 0
  · exact ⟨0, 0, by simp [hn]⟩
  · obtain ⟨a, b, _, _, hab⟩ := arbitrarily_large_quadratic_witnesses n 0 (Nat.pos_of_ne_zero hn)
    exact ⟨a, b, hab⟩
