-- Prove2me | solution 3 for flt_five
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T13:33:28.155936+00:00
-- url     : https://prove2.me/submissions/07e716b5-d0b0-4f98-819c-f016cf26947c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt_five
import Theorems.Thm_flt5_case1
import Theorems.Thm_flt5_descent_case2
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

private lemma coprime_of_eq5 (a b c : ℕ) (h_cop : Nat.Coprime a b) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (ha : 0 < a) : Nat.Coprime a c := by
  rw [Nat.Coprime]
  by_contra h_ne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h_ne
  have hpa : p ∣ a := dvd_trans hpdvd (Nat.gcd_dvd_left a c)
  have hpc : p ∣ c := dvd_trans hpdvd (Nat.gcd_dvd_right a c)
  have hpnb : ¬(p ∣ b) := by
    intro hpb
    have h1 : p ∣ 1 := h_cop ▸ Nat.dvd_gcd hpa hpb
    exact absurd (Nat.le_of_dvd Nat.one_pos h1) (not_le.mpr hp.one_lt)
  apply hpnb ∘ hp.dvd_of_dvd_pow
  have hpc5 : p ∣ c ^ 5 := dvd_pow hpc (by omega)
  rw [← h_eq] at hpc5
  have hpa5 : p ∣ a ^ 5 := dvd_pow hpa (by omega)
  have h1 : (p : ℤ) ∣ (a : ℤ) ^ 5 + (b : ℤ) ^ 5 := by exact_mod_cast hpc5
  have h2 : (p : ℤ) ∣ (a : ℤ) ^ 5 := by exact_mod_cast hpa5
  have h3 : (p : ℤ) ∣ (b : ℤ) ^ 5 := by
    have key := Int.dvd_sub h1 h2
    have heq : (a : ℤ) ^ 5 + (b : ℤ) ^ 5 - (a : ℤ) ^ 5 = (b : ℤ) ^ 5 := by ring
    rwa [heq] at key
  exact_mod_cast h3

-- g^5 ∣ c^5 → g ∣ c in ℕ (via gcd argument, avoiding UFD lemma)
private lemma nat_dvd_of_pow5_dvd {g c : ℕ} (hg : 0 < g) (h : g ^ 5 ∣ c ^ 5) : g ∣ c := by
  set d := Nat.gcd g c with hd_def
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left c hg
  have hd_dvd_g : d ∣ g := Nat.gcd_dvd_left g c
  have hd_dvd_c : d ∣ c := Nat.gcd_dvd_right g c
  set g' := g / d
  set c' := c / d
  have hdg : d * g' = g := Nat.mul_div_cancel' hd_dvd_g
  have hdc : d * c' = c := Nat.mul_div_cancel' hd_dvd_c
  have hg'c'_cop : Nat.Coprime g' c' := Nat.coprime_div_gcd_div_gcd hd_pos
  -- Lift g^5 ∣ c^5 to g'^5 ∣ c'^5
  have hg'5c'5 : g' ^ 5 ∣ c' ^ 5 := by
    have h1 : (d * g') ^ 5 ∣ (d * c') ^ 5 := by rw [hdg, hdc]; exact h
    simp only [mul_pow] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hd_pos 5) h1
  -- Since gcd(g', c') = 1, also gcd(g'^5, c'^5) = 1
  have hcop5 : Nat.Coprime (g' ^ 5) (c' ^ 5) := (hg'c'_cop.pow_left 5).pow_right 5
  -- g'^5 ∣ c'^5 and gcd(g'^5, c'^5) = 1 → g'^5 ∣ 1 → g'^5 = 1
  have hg'5_eq_1 : g' ^ 5 = 1 := by
    have hgcd : Nat.gcd (g' ^ 5) (c' ^ 5) = g' ^ 5 :=
      Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd (dvd_refl _) hg'5c'5)
    have h1 : Nat.gcd (g' ^ 5) (c' ^ 5) = 1 := hcop5
    omega
  -- g'^5 = 1 and g' ≥ 1 → g' = 1
  have hg'_pos : 0 < g' := Nat.div_pos (Nat.le_of_dvd hg hd_dvd_g) hd_pos
  have hg'_eq_1 : g' = 1 := by
    by_contra hne
    have h2 : 2 ≤ g' := by omega
    have hge : 32 ≤ g' ^ 5 := calc
      (32 : ℕ) = 2 ^ 5 := by decide
        _ ≤ g' ^ 5 := Nat.pow_le_pow_left h2 5
    omega
  -- g = d * 1 = d, and d ∣ c
  have hg_eq_d : g = d := by
    have := hdg; rw [hg'_eq_1, Nat.mul_one] at this; exact this.symm
  rw [hg_eq_d]; exact hd_dvd_c

theorem solution (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 := by
  intro h_eq
  set g := Nat.gcd a b
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  set a₀ := a / g
  set b₀ := b / g
  have ha₀_pos : 0 < a₀ := Nat.div_pos (Nat.le_of_dvd ha hga) hg_pos
  have hb₀_pos : 0 < b₀ := Nat.div_pos (Nat.le_of_dvd hb hgb) hg_pos
  have hga_eq : g * a₀ = a := Nat.mul_div_cancel' hga
  have hgb_eq : g * b₀ = b := Nat.mul_div_cancel' hgb
  have h_cop : Nat.Coprime a₀ b₀ := Nat.coprime_div_gcd_div_gcd hg_pos
  have hg5c5 : g ^ 5 ∣ c ^ 5 := by
    have : g ^ 5 ∣ a ^ 5 + b ^ 5 :=
      Nat.dvd_add (pow_dvd_pow_of_dvd hga 5) (pow_dvd_pow_of_dvd hgb 5)
    rwa [h_eq] at this
  have hgc : g ∣ c := nat_dvd_of_pow5_dvd hg_pos hg5c5
  set c₀ := c / g
  have hc₀_pos : 0 < c₀ := Nat.div_pos (Nat.le_of_dvd hc hgc) hg_pos
  have hgc_eq : g * c₀ = c := Nat.mul_div_cancel' hgc
  have h_eq₀ : a₀ ^ 5 + b₀ ^ 5 = c₀ ^ 5 := by
    have hmul : g ^ 5 * (a₀ ^ 5 + b₀ ^ 5) = g ^ 5 * c₀ ^ 5 := by
      calc g ^ 5 * (a₀ ^ 5 + b₀ ^ 5)
          = (g * a₀) ^ 5 + (g * b₀) ^ 5 := by ring
        _ = a ^ 5 + b ^ 5 := by rw [hga_eq, hgb_eq]
        _ = c ^ 5 := h_eq
        _ = (g * c₀) ^ 5 := by rw [hgc_eq]
        _ = g ^ 5 * c₀ ^ 5 := by ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hg_pos 5) hmul
  have h_cop_ac : Nat.Coprime a₀ c₀ := coprime_of_eq5 a₀ b₀ c₀ h_cop h_eq₀ ha₀_pos
  have h_cop_bc : Nat.Coprime b₀ c₀ :=
    coprime_of_eq5 b₀ a₀ c₀ (h_cop.symm) (by rw [add_comm]; exact h_eq₀) hb₀_pos
  have h_eqZ : (a₀ : ℤ) ^ 5 + (b₀ : ℤ) ^ 5 = (c₀ : ℤ) ^ 5 := by exact_mod_cast h_eq₀
  have h_copZ : Int.gcd (a₀ : ℤ) (b₀ : ℤ) = 1 := by
    simp [Int.gcd_natCast_natCast, h_cop]
  by_cases h5c : (5 : ℤ) ∣ (c₀ : ℤ)
  · exact flt5_descent_case2 a₀ b₀ c₀ h_eqZ h_copZ h5c (by exact_mod_cast hc₀_pos.ne')
  · by_cases h5a : (5 : ℤ) ∣ (a₀ : ℤ)
    · apply flt5_descent_case2 (c₀ : ℤ) (-(b₀ : ℤ)) (a₀ : ℤ)
      · have h1 : (-(b₀ : ℤ)) ^ 5 = -(b₀ : ℤ) ^ 5 := by ring
        rw [h1, ← h_eqZ]; ring
      · simp only [Int.gcd, Int.natAbs_neg, Int.natAbs_natCast]
        exact h_cop_bc.symm
      · exact h5a
      · exact_mod_cast ha₀_pos.ne'
    · by_cases h5b : (5 : ℤ) ∣ (b₀ : ℤ)
      · apply flt5_descent_case2 (c₀ : ℤ) (-(a₀ : ℤ)) (b₀ : ℤ)
        · have h1 : (-(a₀ : ℤ)) ^ 5 = -(a₀ : ℤ) ^ 5 := by ring
          rw [h1, ← h_eqZ]; ring
        · simp only [Int.gcd, Int.natAbs_neg, Int.natAbs_natCast]
          exact h_cop_ac.symm
        · exact h5b
        · exact_mod_cast hb₀_pos.ne'
      · exact flt5_case1 a₀ b₀ c₀ h_eqZ h5a h5b h5c
