-- Prove2me | solution 1 for flt7_apb_div_is_7th_pow
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:32:24.524519+00:00
-- url     : https://prove2.me/submissions/6def5f2f-9e34-42e7-b65e-7306273a422d

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

private lemma apb_dvd_sum7 (a b : ℕ) : (a+b) ∣ (a^7+b^7) := by
  have h : (a:ℤ)+b ∣ (a:ℤ)^7+b^7 :=
    ⟨(a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-(a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6, by ring⟩
  exact_mod_cast (show ((a+b:ℕ):ℤ) ∣ ((a^7+b^7:ℕ):ℤ) by push_cast; exact h)

private lemma apb_val6 (a b c c1 : ℕ) (ha : 0 < a) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) :
    padicValNat 7 (a+b) = 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have lte := padicValNat.pow_add_pow (⟨3, rfl⟩ : Odd 7) h7ab h7a (⟨3, rfl⟩ : Odd 7)
  rw [h_eq, padicValNat.pow 7 (Nat.pos_iff_ne_zero.mp hc_pos)] at lte
  have hpc : padicValNat 7 c = 1 := by
    rw [hc, padicValNat.mul (by decide) (by omega), padicValNat.self (by decide),
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h7c1))]
  rw [hpc, Nat.mul_one, padicValNat.self (by decide)] at lte; omega

private lemma seven_dvd_phi (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) :
    7 ∣ (a^7+b^7)/(a+b) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  set φ := (a^7+b^7)/(a+b)
  have hab_ne : a+b ≠ 0 := by omega
  have hprod : (a+b) * φ = a^7+b^7 := Nat.mul_div_cancel' (apb_dvd_sum7 a b)
  have hφ_ne : φ ≠ 0 := by
    intro h; simp [h] at hprod
    exact absurd hprod (by have : 0 < a^7 := pow_pos ha 7; omega)
  have lte := padicValNat.pow_add_pow (⟨3, rfl⟩ : Odd 7) h7ab h7a (⟨3, rfl⟩ : Odd 7)
  rw [h_eq, padicValNat.pow 7 (Nat.pos_iff_ne_zero.mp hc_pos)] at lte
  have hpc : padicValNat 7 c = 1 := by
    rw [hc, padicValNat.mul (by decide) (by omega), padicValNat.self (by decide),
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h7c1))]
  rw [hpc, Nat.mul_one, padicValNat.self (by decide)] at lte
  have hprod_val : padicValNat 7 ((a+b) * φ) =
      padicValNat 7 (a+b) + padicValNat 7 φ := padicValNat.mul hab_ne hφ_ne
  rw [hprod] at hprod_val
  have hsum_val : padicValNat 7 (a^7+b^7) = 7 := by
    rw [h_eq, padicValNat.pow 7 (Nat.pos_iff_ne_zero.mp hc_pos), hpc, Nat.mul_one]
  have hv6 : padicValNat 7 (a+b) = 6 := by omega
  rw [hsum_val, hv6] at hprod_val
  have h71 : 7^1 ∣ φ := (padicValNat_dvd_iff_le hφ_ne).mpr (by omega)
  simpa using h71

private lemma phi7_int_eq (a b : ℕ) (hab_ne : a+b ≠ 0) :
    (((a^7+b^7)/(a+b):ℕ):ℤ) = (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-
        (a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6 := by
  have hprod := Nat.mul_div_cancel' (apb_dvd_sum7 a b)
  have hab_ne_int : (a:ℤ)+b ≠ 0 := by exact_mod_cast hab_ne
  apply mul_left_cancel₀ hab_ne_int
  have h1 : ((a:ℤ)+b) * (((a^7+b^7)/(a+b):ℕ):ℤ) = (a:ℤ)^7+b^7 := by
    have : (((a+b) * ((a^7+b^7)/(a+b)):ℕ):ℤ) = ((a^7+b^7:ℕ):ℤ) := by exact_mod_cast hprod
    push_cast at this ⊢; linarith
  rw [h1]; ring

private lemma gcd7_exact (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.gcd (a+b) ((a^7+b^7)/(a+b)) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hab_ne : a+b ≠ 0 := by omega
  have hub : Nat.gcd (a+b) ((a^7+b^7)/(a+b)) ∣ 7 := by
    set g := Nat.gcd (a+b) ((a^7+b^7)/(a+b))
    have hgab : g ∣ a+b := Nat.gcd_dvd_left _ _
    have hgphi : g ∣ (a^7+b^7)/(a+b) := Nat.gcd_dvd_right _ _
    have heq := phi7_int_eq a b hab_ne
    have hg7a6 : g ∣ 7*a^6 := by
      have hq_int : (g:ℤ) ∣ 7*(a:ℤ)^6 := by
        have hgab_int : (g:ℤ) ∣ (a:ℤ)+b := by exact_mod_cast hgab
        have hgphi_int : (g:ℤ) ∣ (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-(a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6 :=
          heq ▸ (by exact_mod_cast hgphi)
        have hident : (a:ℤ)+b ∣ (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-(a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6-7*(a:ℤ)^6 :=
          ⟨-6*(a:ℤ)^5+5*(a:ℤ)^4*b-4*(a:ℤ)^3*b^2+3*(a:ℤ)^2*b^3-2*(a:ℤ)*b^4+b^5, by ring⟩
        have h2 := dvd_sub hgphi_int (dvd_trans hgab_int hident)
        convert h2 using 1; ring
      exact_mod_cast hq_int
    have hcop_apb_a : Nat.Coprime (a+b) a := Nat.coprime_self_add_left.mpr hcop.symm
    exact ((hcop_apb_a.coprime_dvd_left hgab).pow_right 6).dvd_of_dvd_mul_right hg7a6
  have hlb : 7 ∣ Nat.gcd (a+b) ((a^7+b^7)/(a+b)) :=
    Nat.dvd_gcd h7ab (seven_dvd_phi a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1)
  exact Nat.dvd_antisymm hub hlb

private lemma coprime_components (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.Coprime ((a+b)/7^6) ((a^7+b^7)/(a+b)/7) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hab_ne : a+b ≠ 0 := by omega
  have hv6 : padicValNat 7 (a+b) = 6 := apb_val6 a b c c1 ha hc_pos h_eq h7a h7ab hc h7c1
  have h_apb_div : 7^6 ∣ a+b := (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have h_phi_div : 7 ∣ (a^7+b^7)/(a+b) := seven_dvd_phi a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  have hgcd7 := gcd7_exact a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1 hcop
  set A := (a+b)/7^6; set B := (a^7+b^7)/(a+b)/7
  have h7A : ¬7 ∣ A := by
    intro ⟨k, hk⟩
    have hv : 7^7 ∣ a+b := calc 7^7 = 7^6 * 7 := by ring
        _ ∣ 7^6 * A := Nat.mul_dvd_mul_left _ ⟨k, hk⟩
        _ = a+b := Nat.mul_div_cancel' h_apb_div
    linarith [(padicValNat_dvd_iff_le hab_ne).mp hv]
  unfold Nat.Coprime
  set g := Nat.gcd A B
  have hgA := Nat.gcd_dvd_left A B; have hgB := Nat.gcd_dvd_right A B
  have hg7 : g ∣ 7 := hgcd7 ▸ Nat.dvd_gcd
    ((Nat.mul_div_cancel' h_apb_div) ▸ dvd_mul_of_dvd_right hgA (7^6))
    ((Nat.mul_div_cancel' h_phi_div) ▸ dvd_mul_of_dvd_right hgB 7)
  rcases (by decide : Nat.Prime 7).eq_one_or_self_of_dvd g hg7 with h1 | h7
  · exact h1
  · exact absurd h7 (fun hg => h7A (hg ▸ hgA))

private lemma descent_eq (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) :
    ((a+b)/7^6) * ((a^7+b^7)/(a+b)/7) = c1^7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hab_ne : a+b ≠ 0 := by omega
  have hv6 : padicValNat 7 (a+b) = 6 := apb_val6 a b c c1 ha hc_pos h_eq h7a h7ab hc h7c1
  have h_apb_div : 7^6 ∣ a+b := (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have h_phi_div : 7 ∣ (a^7+b^7)/(a+b) := seven_dvd_phi a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 7^7)
  calc 7^7 * (((a+b)/7^6) * ((a^7+b^7)/(a+b)/7))
      = (7^6 * ((a+b)/7^6)) * (7 * ((a^7+b^7)/(a+b)/7)) := by ring
    _ = (a+b) * ((a^7+b^7)/(a+b)) := by
          rw [Nat.mul_div_cancel' h_apb_div, Nat.mul_div_cancel' h_phi_div]
    _ = a^7+b^7 := Nat.mul_div_cancel' (apb_dvd_sum7 a b)
    _ = (7*c1)^7 := by rw [← hc]; exact h_eq
    _ = 7^7 * c1^7 := by ring

-- (a+b)/7^6 is a perfect 7th power in the FLT-7 setting
theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1)
    (hcop : Nat.Coprime a b) :
    ∃ d : ℕ, (a+b) / 7^6 = d^7 := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  set A := (a+b) / 7^6
  set B := (a^7+b^7)/(a+b) / 7
  have hab_ne : a+b ≠ 0 := by omega
  have hcop_AB := coprime_components a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1 hcop
  have hprod_AB := descent_eq a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  have hv6 : padicValNat 7 (a+b) = 6 := apb_val6 a b c c1 ha hc_pos h_eq h7a h7ab hc h7c1
  have h_apb_div : 7^6 ∣ a+b := (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have hA_pos : 0 < A := by
    simp only [A]
    exact Nat.div_pos (Nat.le_of_dvd (by omega) h_apb_div) (by positivity)
  have hc1_pos : 0 < c1 := by rw [hc] at hc_pos; omega
  have hB_pos : 0 < B := by
    have hpos : 0 < A * B := hprod_AB ▸ pow_pos hc1_pos 7
    rcases Nat.eq_zero_or_pos B with hB0 | hB
    · simp [hB0] at hpos
    · exact hB
  have hcop_int : IsCoprime (A:ℤ) (B:ℤ) := hcop_AB.isCoprime
  have hprod_int : (A:ℤ) * (B:ℤ) = (c1:ℤ)^7 := by exact_mod_cast hprod_AB
  obtain ⟨d_int, hd⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop_int (⟨3, rfl⟩ : Odd 7) hprod_int
  have h7pos : (0:ℤ) < d_int^7 := hd.symm ▸ (by exact_mod_cast hA_pos)
  have hd_pos : 0 < d_int := by
    rcases lt_or_ge 0 d_int with hd' | hd'
    · exact hd'
    · have h6 : 0 ≤ d_int^6 := by rw [show d_int^6 = (d_int^3)^2 from by ring]; exact sq_nonneg _
      linarith [show d_int * d_int^6 = d_int^7 from by ring, mul_nonpos_of_nonpos_of_nonneg hd' h6]
  use d_int.toNat
  have hd_nat : (d_int.toNat : ℤ) = d_int := Int.toNat_of_nonneg hd_pos.le
  have : (d_int.toNat^7 : ℤ) = (A : ℤ) := by push_cast [hd_nat]; exact hd.symm
  exact_mod_cast this.symm
