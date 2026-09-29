-- Prove2me | solution 1 for EtaHead.Jet.zpow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:37:26.304296+00:00
-- url     : https://prove2.me/submissions/e51f68d1-afb8-49e6-be61-9d59b3bd8177

import Mathlib
import Definitions.Def_Tropical_EtaQuotientHeadCoeff

open PowerSeries EtaHead in
theorem solution {u : (PowerSeries ℤ)ˣ} {c1 c2 : ℤ} (hu : Jet (u : PowerSeries ℤ) c1 c2) :
    ∀ n : ℤ, Jet ((u ^ n : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (n * c1) (n * c2 + Tri n * c1 ^ 2) := by
  -- low-order coefficients of a product
  have k1 : ∀ f g : PowerSeries ℤ,
      coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
    intro f g
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ]
  have k2 : ∀ f g : PowerSeries ℤ,
      coeff 2 (f * g) = coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
    intro f g
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ]
  have hc : ∀ f : PowerSeries ℤ, constantCoeff f = coeff 0 f :=
    fun f => (coeff_zero_eq_constantCoeff_apply f).symm
  have hmul : ∀ (f g : PowerSeries ℤ) (a1 a2 b1 b2 : ℤ), Jet f a1 a2 → Jet g b1 b2 →
      Jet (f * g) (a1 + b1) (a2 + b2 + a1 * b1) := by
    rintro f g a1 a2 b1 b2 ⟨f0, f1, f2⟩ ⟨g0, g1, g2⟩
    rw [hc] at f0 g0
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, hc f, hc g, f0, g0, mul_one]
    · rw [k1, f0, g0, f1, g1]; ring
    · rw [k2, f0, g0, f1, g1, f2, g2]; ring
  have hT2 : ∀ n : ℤ, Tri n * 2 = n * (n - 1) := fun n =>
    Int.ediv_mul_cancel (even_iff_two_dvd.1 (Int.even_mul_pred_self n))
  have hnat : ∀ m : ℕ, Jet ((u ^ m : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      (m * c1) (m * c2 + Tri m * c1 ^ 2) := by
    intro m
    induction m with
    | zero =>
      have h0 : Tri 0 = 0 := by simp [Tri]
      simp only [pow_zero, Units.val_one, Nat.cast_zero, zero_mul, h0, zero_add]
      refine ⟨by simp, ?_, ?_⟩ <;> simp [coeff_one]
    | succ m ih =>
      have h := hmul _ _ _ _ _ _ ih hu
      rw [pow_succ, Units.val_mul]
      obtain ⟨h0, h1, h2⟩ := h
      refine ⟨h0, ?_, ?_⟩
      · rw [h1]; push_cast; ring
      · rw [h2]
        have e1 := hT2 m
        have e2 := hT2 ((m : ℤ) + 1)
        have : Tri ((m : ℤ) + 1) = Tri m + m := by
          apply mul_right_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
          rw [e2]
          linear_combination (-1 : ℤ) * e1
        push_cast
        rw [this]; ring
  have hinv : ∀ (v : (PowerSeries ℤ)ˣ) (a b : ℤ), Jet (v : PowerSeries ℤ) a b →
      Jet ((v⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (-a) (a ^ 2 - b) := by
    rintro v a b ⟨v0, v1, v2⟩
    have hvv : ((v⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) * v = 1 := Units.inv_mul v
    have e0 := congrArg constantCoeff hvv
    have e1 := congrArg (coeff 1) hvv
    have e2 := congrArg (coeff 2) hvv
    rw [map_mul, map_one, v0, mul_one] at e0
    have w0 : coeff 0 ((v⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by rw [← hc]; exact e0
    have vv0 : coeff 0 (v : PowerSeries ℤ) = 1 := by rw [← hc]; exact v0
    have o1 : coeff 1 (1 : PowerSeries ℤ) = 0 := by simp [coeff_one]
    have o2 : coeff 2 (1 : PowerSeries ℤ) = 0 := by simp [coeff_one]
    rw [k1, w0, vv0, v1, o1] at e1
    rw [k2, w0, vv0, v1, v2, o2] at e2
    have hw1 : coeff 1 ((v⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = -a := by linarith
    refine ⟨e0, hw1, ?_⟩
    rw [hw1] at e2
    linear_combination e2
  intro n
  cases n with
  | ofNat m =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hnat m
  | negSucc m =>
    rw [zpow_negSucc]
    obtain ⟨h0, h1, h2⟩ := hinv _ _ _ (hnat (m + 1))
    refine ⟨h0, ?_, ?_⟩
    · rw [h1, Int.negSucc_eq]; push_cast; ring
    · rw [h2, Int.negSucc_eq]
      have e1 := hT2 ((m : ℤ) + 1)
      have e2 := hT2 (-((m : ℤ) + 1))
      have : Tri (-((m : ℤ) + 1)) = Tri ((m : ℤ) + 1) + ((m : ℤ) + 1) := by
        apply mul_right_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
        rw [e2]
        linear_combination (-1 : ℤ) * e1
      push_cast
      rw [this]
      linear_combination (-c1 ^ 2) * e1
