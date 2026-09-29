-- Prove2me | solution 1 for Moebius.ZM.irreducible_mk_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T15:03:28.53876+00:00
-- url     : https://prove2.me/submissions/224b01f3-4d7e-4799-95a6-7b9ffb408974

import Definitions.Def_MachineLearning_MoebiusTwistRing
open Moebius Moebius.ZM in
theorem solution (n : ℤ) : Irreducible (mk n 0) ↔ n = 2 ∨ n = -2 := by
  have hcoe : ((mk n 0 : ZM) : ℤ × ℤ) = (n, n) := by simp [mk]
  have hunit : ∀ z : ZM, IsUnit z →
      ((z : ℤ × ℤ).1 = 1 ∨ (z : ℤ × ℤ).1 = -1) ∧ ((z : ℤ × ℤ).2 = 1 ∨ (z : ℤ × ℤ).2 = -1) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    have h := congrArg Subtype.val hw
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    have h1 : (z : ℤ × ℤ).1 * (w : ℤ × ℤ).1 = 1 := congrArg Prod.fst h
    have h2 : (z : ℤ × ℤ).2 * (w : ℤ × ℤ).2 = 1 := congrArg Prod.snd h
    exact ⟨Int.eq_one_or_neg_one_of_mul_eq_one h1, Int.eq_one_or_neg_one_of_mul_eq_one h2⟩
  have hunit_of : ∀ z : ZM, ((z : ℤ × ℤ).1 = 1 ∨ (z : ℤ × ℤ).1 = -1) →
      ((z : ℤ × ℤ).2 = 1 ∨ (z : ℤ × ℤ).2 = -1) → IsUnit z := by
    intro z h1 h2
    refine isUnit_iff_exists_inv.mpr ⟨z, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    ext
    · rcases h1 with h | h <;> simp [h]
    · rcases h2 with h | h <;> simp [h]
  have hfac : ∀ (x₁ y₁ x₂ y₂ : ℤ) (h₁ : Even (x₁ - y₁)) (h₂ : Even (x₂ - y₂)),
      x₁ * x₂ = n → y₁ * y₂ = n →
      mk n 0 = (⟨(x₁, y₁), h₁⟩ : ZM) * (⟨(x₂, y₂), h₂⟩ : ZM) := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hx hy
    apply Subtype.ext
    rw [hcoe]
    simp only [MulMemClass.coe_mul, Prod.mk_mul_mk, hx, hy]
  -- an odd divisor of ±2 is ±1
  have hodd : ∀ x y : ℤ, x % 2 = 1 → (x * y = 2 ∨ x * y = -2) → x = 1 ∨ x = -1 := by
    intro x y hx hxy
    have hmul : x.natAbs * y.natAbs = 2 := by
      rcases hxy with h | h
      · rw [← Int.natAbs_mul, h]; rfl
      · rw [← Int.natAbs_mul, h]; rfl
    have hle : x.natAbs ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨y.natAbs, hmul.symm⟩
    rcases Int.natAbs_eq x with h | h
    · interval_cases hm : x.natAbs <;> omega
    · interval_cases hm : x.natAbs <;> omega
  constructor
  · intro hirr
    have hnu := hirr.not_isUnit
    by_contra hne
    push Not at hne
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · by_cases hk0 : k = 0
      · apply hirr.ne_zero
        apply Subtype.ext
        rw [hcoe]
        simp [hk, hk0]
      rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · rcases hirr.isUnit_or_isUnit (hfac 2 2 k k ⟨0, by norm_num⟩ ⟨0, by ring⟩ (by omega) (by omega))
          with hu | hu
        · have := (hunit _ hu).1
          simp at this
        · have := (hunit _ hu).1
          simp only at this
          omega
      · rcases hirr.isUnit_or_isUnit
          (hfac (2 * k) 2 1 k ⟨k - 1, by ring⟩ ⟨-j, by omega⟩ (by omega) (by omega)) with hu | hu
        · have := (hunit _ hu).1
          simp only at this
          omega
        · have := (hunit _ hu).2
          simp only at this
          omega
    · by_cases hn1 : n = 1 ∨ n = -1
      · apply hnu
        apply hunit_of
        · rw [hcoe]; exact hn1
        · rw [hcoe]; exact hn1
      push Not at hn1
      rcases hirr.isUnit_or_isUnit (hfac n 1 1 n ⟨k, by omega⟩ ⟨-k, by omega⟩ (by ring) (by ring))
        with hu | hu
      · have := (hunit _ hu).1
        simp only at this
        omega
      · have := (hunit _ hu).2
        simp only at this
        omega
  · intro hn2
    rw [irreducible_iff]
    refine ⟨fun hu => ?_, ?_⟩
    · have := (hunit _ hu).1
      rw [hcoe] at this
      simp only at this
      omega
    · rintro ⟨⟨a₁, a₂⟩, ha⟩ ⟨⟨b₁, b₂⟩, hb⟩ hab
      have h := congrArg Subtype.val hab
      rw [hcoe] at h
      simp only [MulMemClass.coe_mul, Prod.mk_mul_mk, Prod.mk.injEq] at h
      have ha' : Even (a₁ - a₂) := ha
      have hb' : Even (b₁ - b₂) := hb
      obtain ⟨ra, hra⟩ := ha'
      obtain ⟨rb, hrb⟩ := hb'
      have h1 : a₁ * b₁ = 2 ∨ a₁ * b₁ = -2 := by rcases hn2 with rfl | rfl <;> [left; right] <;> exact h.1.symm
      have h2 : a₂ * b₂ = 2 ∨ a₂ * b₂ = -2 := by rcases hn2 with rfl | rfl <;> [left; right] <;> exact h.2.symm
      rcases Int.emod_two_eq_zero_or_one a₁ with ha1 | ha1
      · -- a₁ even, so b₁ odd, b₂ odd
        have hb1 : b₁ % 2 = 1 := by
          rcases Int.emod_two_eq_zero_or_one b₁ with hb1 | hb1
          · exfalso
            obtain ⟨s, hs⟩ : ∃ s, a₁ = 2 * s := ⟨a₁ / 2, by omega⟩
            obtain ⟨t, ht⟩ : ∃ t, b₁ = 2 * t := ⟨b₁ / 2, by omega⟩
            rw [hs, ht] at h1
            have : (s * t) * 4 = 2 ∨ (s * t) * 4 = -2 := by
              rcases h1 with h | h
              · left; linarith
              · right; linarith
            omega
          · exact hb1
        have hb2 : b₂ % 2 = 1 := by omega
        right
        apply hunit_of
        · exact hodd b₁ a₁ hb1 (by rw [mul_comm]; exact h1)
        · exact hodd b₂ a₂ hb2 (by rw [mul_comm]; exact h2)
      · have ha2 : a₂ % 2 = 1 := by omega
        left
        apply hunit_of
        · exact hodd a₁ b₁ ha1 h1
        · exact hodd a₂ b₂ ha2 h2
