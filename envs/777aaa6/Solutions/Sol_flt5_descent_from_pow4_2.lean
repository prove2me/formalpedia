-- Prove2me | solution 2 for flt5_descent_from_pow4
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T16:21:04.792322+00:00
-- url     : https://prove2.me/submissions/9f90089e-993c-4a40-ba94-ba3459f941d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_descent_construction
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Sketch: flt5_descent_from_pow4 (sorry-free, inlines gcd(w,v)=1)
-- Child: flt5_descent_construction

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0)
    (h54 : (5 : ℤ) ^ 4 ∣ a + b) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  obtain ⟨w, hw⟩ := h54
  obtain ⟨c1, hc1⟩ := h5c
  have h5c : (5 : ℤ) ∣ c := ⟨c1, hc1⟩
  -- v such that Phi = 5*v
  have hPhi_eq : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 =
      5 * (5 ^ 15 * w ^ 4 - 5 ^ 8 * w ^ 2 * (a * b) + (a * b) ^ 2) := by
    have h_b : b = 5 ^ 4 * w - a := by rw [← hw]; ring
    rw [h_b]; ring
  obtain ⟨v, hPhi⟩ : ∃ v : ℤ,
      a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v :=
    ⟨5 ^ 15 * w ^ 4 - 5 ^ 8 * w ^ 2 * (a * b) + (a * b) ^ 2, hPhi_eq⟩
  -- w * v = c1^5
  have hwv : w * v = c1 ^ 5 := by
    have key : (5 : ℤ) ^ 5 * (w * v) = (5 : ℤ) ^ 5 * c1 ^ 5 :=
      calc (5 : ℤ) ^ 5 * (w * v)
          = (5 ^ 4 * w) * (5 * v) := by ring
        _ = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
              rw [hw, hPhi]
        _ = a ^ 5 + b ^ 5 := by ring
        _ = c ^ 5 := h_eq
        _ = (5 * c1) ^ 5 := by rw [hc1]
        _ = (5 : ℤ) ^ 5 * c1 ^ 5 := by ring
    exact mul_left_cancel₀ (show (5 : ℤ) ^ 5 ≠ 0 from by decide) key
  -- gcd(w, v) = 1 (inline proof)
  have hcop_wv : Int.gcd w v = 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have euclid5 : ∀ x y : ℤ, (5 : ℤ) ∣ x * y → ¬(5 : ℤ) ∣ y → (5 : ℤ) ∣ x := by
      intro x y hxy hny
      have mul0 : ∀ a b : ZMod 5, a * b = 0 → b ≠ 0 → a = 0 := by decide
      have hxy0 : (x : ZMod 5) * (y : ZMod 5) = 0 := by
        have h : ((x * y : ℤ) : ZMod 5) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hxy
        push_cast at h; exact h
      have hy0 : (y : ZMod 5) ≠ 0 := by
        intro h; rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h; exact hny (by exact_mod_cast h)
      have hx0 := mul0 _ _ hxy0 hy0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0; exact_mod_cast hx0
    have dvd_igcd : ∀ (k x y : ℤ), k ∣ x → k ∣ y → k ∣ ↑(Int.gcd x y) := by
      intro k x y hkx hky
      have hkx' : k.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hkx
      have hky' : k.natAbs ∣ y.natAbs := Int.natAbs_dvd_natAbs.mpr hky
      have h : k.natAbs ∣ Int.gcd x y := Nat.dvd_gcd hkx' hky'
      exact Int.natAbs_dvd.mp (by exact_mod_cast h)
    by_contra h_ne1
    obtain ⟨p, hp_prime, hp_dvd_gcd⟩ := Nat.exists_prime_and_dvd h_ne1
    have hp_dvd_w : (p : ℤ) ∣ w := dvd_trans
      (by exact_mod_cast hp_dvd_gcd : (p : ℤ) ∣ ↑(Int.gcd w v)) (Int.gcd_dvd_left w v)
    have hp_dvd_v : (p : ℤ) ∣ v := dvd_trans
      (by exact_mod_cast hp_dvd_gcd : (p : ℤ) ∣ ↑(Int.gcd w v)) (Int.gcd_dvd_right w v)
    have hp_dvd_ab : (p : ℤ) ∣ a + b :=
      dvd_trans hp_dvd_w ⟨5 ^ 4, by rw [hw]; ring⟩
    have hp_dvd_Phi : (p : ℤ) ∣ a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
      rw [hPhi]; exact dvd_mul_of_dvd_right hp_dvd_v 5
    have hp_dvd_5a4 : (p : ℤ) ∣ 5 * a ^ 4 := by
      have h1 : (p : ℤ) ∣ (a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*a^4 :=
        dvd_trans hp_dvd_ab ⟨-4*a^3+3*a^2*b-2*a*b^2+b^3, by ring⟩
      have h2 := dvd_sub hp_dvd_Phi h1
      rwa [show (a^4-a^3*b+a^2*b^2-a*b^3+b^4) -
          ((a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*a^4) = 5*a^4 from by ring] at h2
    have hp_na : ¬ (p : ℤ) ∣ a := by
      intro hpa
      have hpb : (p : ℤ) ∣ b := by
        have h := dvd_sub hp_dvd_ab hpa; rwa [show a+b-a=b from by ring] at h
      have h1 : (p : ℤ) ∣ ↑(Int.gcd a b) := dvd_igcd _ a b hpa hpb
      rw [h_cop, Nat.cast_one] at h1
      linarith [Int.le_of_dvd one_pos h1, show 2 ≤ (p : ℤ) from by exact_mod_cast hp_prime.two_le]
    have hp_dvd_5 : p ∣ 5 := by
      have h_dvd_nat : p ∣ 5 * a.natAbs ^ 4 := by
        have h := Int.natAbs_dvd_natAbs.mpr hp_dvd_5a4
        simp only [Int.natAbs_mul, Int.natAbs_pow] at h; exact_mod_cast h
      rcases hp_prime.dvd_mul.mp h_dvd_nat with h5 | h4
      · exact h5
      · exfalso; apply hp_na
        exact Int.natAbs_dvd_natAbs.mp (by exact_mod_cast hp_prime.dvd_of_dvd_pow h4)
    have hp_eq_5 : p = 5 :=
      (Nat.Prime.eq_one_or_self_of_dvd (by decide) p hp_dvd_5).resolve_left hp_prime.one_lt.ne'
    subst hp_eq_5
    obtain ⟨w0, hw0⟩ := hp_dvd_w; obtain ⟨v0, hv0⟩ := hp_dvd_v
    have hab_55 : a + b = 5 ^ 5 * w0 := by rw [hw, hw0]; ring
    have h_Phi_mod : (5 : ℤ) ^ 2 ∣ (a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*(a*b)^2 :=
      ⟨5^18 * w0^4 - 5^9 * w0^2 * (a*b), by
        have heq : a^4-a^3*b+a^2*b^2-a*b^3+b^4 - 5*(a*b)^2 = (a+b)^4 - 5*(a+b)^2*(a*b) := by ring
        rw [heq, hab_55]; ring⟩
    have h52_Phi : (5 : ℤ)^2 ∣ a^4-a^3*b+a^2*b^2-a*b^3+b^4 := ⟨v0, by rw [hPhi, hv0]; ring⟩
    have h5_ab2 : (5 : ℤ) ∣ (a*b)^2 := by
      have h52 : (5 : ℤ)^2 ∣ 5*(a*b)^2 := by
        have h := dvd_sub h52_Phi h_Phi_mod
        rwa [show (a^4-a^3*b+a^2*b^2-a*b^3+b^4) -
            ((a^4-a^3*b+a^2*b^2-a*b^3+b^4) - 5*(a*b)^2) = 5*(a*b)^2 from by ring] at h
      obtain ⟨k, hk⟩ := h52
      have h25 : (5:ℤ)^2 = 25 := by norm_num
      have hcanc : 5 * (a*b)^2 = 5 * (5 * k) := by linarith
      exact ⟨k, mul_left_cancel₀ (show (5:ℤ) ≠ 0 from by norm_num) hcanc⟩
    have h5_ab : (5 : ℤ) ∣ a * b := by
      by_contra h5nab
      exact h5nab (euclid5 (a*b) (a*b) (by rwa [show a*b*(a*b)=(a*b)^2 from by ring]) h5nab)
    have h5_a_or_b : (5 : ℤ) ∣ a ∨ (5 : ℤ) ∣ b := by
      by_contra h; push_neg at h
      exact h.1 (euclid5 a b h5_ab h.2)
    have h5_sum : (5 : ℤ) ∣ a + b := ⟨5^4 * w0, by rw [hab_55]; ring⟩
    have aux : (5:ℤ) ∣ a → (5:ℤ) ∣ b → False := fun h5x h5y => by
      have h1 := dvd_igcd _ a b h5x h5y
      rw [h_cop, Nat.cast_one] at h1
      linarith [Int.le_of_dvd one_pos h1]
    rcases h5_a_or_b with h5a | h5b
    · apply aux h5a
      have h := dvd_sub h5_sum h5a; rwa [show a+b-a=b from by ring] at h
    · apply aux _ h5b
      have h := dvd_sub h5_sum h5b; rwa [show a+b-b=a from by ring] at h
  -- Delegate to flt5_descent_construction
  exact flt5_descent_construction a b c w v c1 h_eq h_cop h5c hc hc1 hw hPhi hwv hcop_wv
