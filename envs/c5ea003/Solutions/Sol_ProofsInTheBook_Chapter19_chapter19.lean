-- Prove2me | solution 1 for ProofsInTheBook.Chapter19.chapter19
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:12:59.505432+00:00
-- url     : https://prove2.me/submissions/7ed1710f-433a-4907-a333-72a26fdb69a8

import Mathlib.Topology.Algebra.Polynomial
import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter19


/-!
# Chapter 19: The fundamental theorem of algebra

From "Proofs from THE BOOK":

**FTA**: Every non-constant polynomial with complex coefficients has a root.

The book presents a proof using the minimum modulus principle:
Consider |p(z)| for a polynomial p of degree n ≥ 1. Since |p(z)| → ∞
as |z| → ∞, the minimum of |p(z)| is attained at some z₀. If |p(z₀)| > 0,
write p(z₀ + w) = p(z₀) + cₘwᵐ + higher terms (m ≥ 1). Choosing w
to make cₘwᵐ point opposite to p(z₀) reduces |p(z₀ + w)| < |p(z₀)|,
contradicting minimality.
-/

namespace ProofsInTheBook.Chapter19

open Polynomial Bornology



theorem shiftedPolynomial_eval (p : ℂ[X]) (z₀ w : ℂ) :
    (shiftedPolynomial p z₀).eval w = p.eval (w + z₀) := by
  simp [shiftedPolynomial]

theorem shiftedPolynomial_eval_zero (p : ℂ[X]) (z₀ : ℂ) :
    (shiftedPolynomial p z₀).eval 0 = p.eval z₀ := by
  simpa using shiftedPolynomial_eval p z₀ 0

theorem shiftedPolynomial_coeff_zero (p : ℂ[X]) (z₀ : ℂ) :
    (shiftedPolynomial p z₀).coeff 0 = p.eval z₀ := by
  rw [Polynomial.coeff_zero_eq_eval_zero, shiftedPolynomial_eval_zero]



/--
After removing the constant term, a nonzero polynomial has a first nonzero
coefficient, and it occurs in positive degree.
-/
lemma exists_first_nonzero_coeff_of_sub_C_eval_zero_ne_zero {q : ℂ[X]}
    (hr : q - Polynomial.C (q.eval 0) ≠ 0) :
    ∃ m : ℕ,
      0 < m ∧
      (q - Polynomial.C (q.eval 0)).coeff m ≠ 0 ∧
      ∀ j : ℕ, j < m → (q - Polynomial.C (q.eval 0)).coeff j = 0 := by
  classical
  let r : ℂ[X] := q - Polynomial.C (q.eval 0)
  have hr_ne : r ≠ 0 := by simpa [r] using hr
  have hs : r.support.Nonempty := Polynomial.support_nonempty.mpr hr_ne
  let m := r.support.min' hs
  refine ⟨m, ?_, ?_, ?_⟩
  · have h0coeff : r.coeff 0 = 0 := by
      simp [r, Polynomial.coeff_zero_eq_eval_zero]
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hm_mem : m ∈ r.support := Finset.min'_mem _ _
    have hm_ne : r.coeff m ≠ 0 := by
      simpa [Polynomial.mem_support_iff] using hm_mem
    exact hm_ne (by simpa [hm0] using h0coeff)
  · have hm_mem : m ∈ r.support := Finset.min'_mem _ _
    simpa [r, Polynomial.mem_support_iff] using hm_mem
  · intro j hj
    by_contra hcoeff
    have hjmem : j ∈ r.support := by
      simpa [Polynomial.mem_support_iff] using hcoeff
    have hmin : m ≤ j := Finset.min'_le _ _ hjmem
    omega



/-- Complex m-th root extraction: for any `z : ℂ` and `m > 0`, ∃ ζ with ζ^m = z. -/
theorem exists_complex_nth_root (z : ℂ) (m : ℕ) (hm : 0 < m) :
    ∃ ζ : ℂ, ζ ^ m = z :=
  ⟨z ^ ((m : ℂ)⁻¹), by simpa using Complex.cpow_nat_inv_pow z hm.ne'⟩

lemma poly_decompose (r : ℂ[X]) (a c : ℂ) (m : ℕ) (hm0 : 0 < m)
    (hconst : r.coeff 0 = a)
    (hbelow : ∀ k, 0 < k → k < m → r.coeff k = 0)
    (hm : r.coeff m = c) :
    ∃ q : ℂ[X], r = C a + C c * X^m + X^(m+1) * q := by
  have hdvd : X^(m+1) ∣ (r - (C a + C c * X^m)) := by
    rw [X_pow_dvd_iff]
    intro i hi
    have hi_le : i ≤ m := by omega
    rcases lt_trichotomy i m with h | h | h
    · rcases eq_or_ne i 0 with hi0 | hi0
      · rw [hi0]
        simp only [coeff_sub, coeff_add]
        have h1 : (C a).coeff 0 = a := by simp
        have h2 : (C c * X^m).coeff 0 = 0 := by
          rw [coeff_C_mul, coeff_X_pow]
          have : 0 ≠ m := by omega
          simp [this]
        rw [h1, h2, hconst]
        ring
      · simp only [coeff_sub, coeff_add]
        have h1 : (C a).coeff i = 0 := by
          rw [coeff_C]; split_ifs with h_eq
          · exfalso; exact hi0 h_eq
          · rfl
        have h2 : (C c * X^m).coeff i = 0 := by
          rw [coeff_C_mul, coeff_X_pow]
          have : i ≠ m := by omega
          simp [this]
        have hr : r.coeff i = 0 := hbelow i (by omega) h
        rw [hr, h1, h2]
        ring
    · rw [h]
      simp only [coeff_sub, coeff_add]
      have h1 : (C a).coeff m = 0 := by
        rw [coeff_C]; split_ifs with h_eq
        · exfalso; exact ne_of_gt hm0 h_eq
        · rfl
      have h2 : (C c * X^m).coeff m = c := by
        rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
      rw [h1, h2, hm]
      ring
    · omega
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, ?_⟩
  calc r = (r - (C a + C c * X^m)) + (C a + C c * X^m) := by ring
       _ = X^(m+1) * q + (C a + C c * X^m) := by rw [hq]
       _ = C a + C c * X^m + X^(m+1) * q := by ring

/--
Analytic local norm-decrease lemma: given a polynomial `r` with constant term
`a ≠ 0`, first nonzero higher coefficient `c` at degree `m > 0`, there exists
`w` with `‖r.eval w‖ < ‖a‖`.
-/
theorem complex_poly_local_norm_decrease
    (r : ℂ[X]) (a c : ℂ) (m : ℕ)
    (hm0 : 0 < m)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hconst : r.coeff 0 = a)
    (hbelow : ∀ k, 0 < k → k < m → r.coeff k = 0)
    (hm : r.coeff m = c) :
    ∃ w : ℂ, ‖r.eval w‖ < ‖a‖ := by
  obtain ⟨ζ, hζ⟩ := exists_complex_nth_root (-a / c) m hm0
  have hcζ : c * ζ ^ m = -a := by
    rw [hζ]; field_simp
  
  obtain ⟨q, hq⟩ := poly_decompose r a c m hm0 hconst hbelow hm
  
  have h_cont : Continuous (fun (t : ℝ) => ‖(ζ^(m+1)) * q.eval ((t:ℂ) * ζ)‖) := by
    fun_prop
  
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have h_nonempty : (Set.Icc (0:ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  obtain ⟨t_max, _, h_max⟩ := IsCompact.exists_isMaxOn h_compact h_nonempty h_cont.continuousOn
  
  set M : ℝ := ‖(ζ^(m+1)) * q.eval ((t_max:ℂ) * ζ)‖ with hM_def
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  
  set t : ℝ := min (1/2) (‖a‖ / (2 * (M + 1))) with ht_def
  have ht_pos : 0 < t := by
    apply lt_min; · norm_num
    · apply div_pos (norm_pos_iff.mpr ha)
      positivity
  have ht_le_half : t ≤ 1/2 := min_le_left _ _
  have ht_le_one : t ≤ 1 := le_trans ht_le_half (by norm_num)
  have ht_le_bound : t ≤ ‖a‖ / (2 * (M + 1)) := min_le_right _ _

  refine ⟨(t : ℂ) * ζ, ?_⟩
  
  have h_eval : r.eval ((t : ℂ) * ζ) = a * (1 - (t : ℂ)^m) + (t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ)) := by
    rw [hq]
    simp only [eval_add, eval_C, eval_mul, eval_X_pow]
    rw [mul_pow, mul_pow]
    have h_c_zeta : c * ((t : ℂ)^m * ζ^m) = (t : ℂ)^m * (c * ζ^m) := by ring
    rw [h_c_zeta, hcζ]
    ring
  
  rw [h_eval]
  
  have ht_m_real : (t : ℂ)^m = ((t^m : ℝ) : ℂ) := by push_cast; rfl
  have ht_m1_real : (t : ℂ)^(m+1) = ((t^(m+1) : ℝ) : ℂ) := by push_cast; rfl
  
  have h_triangle := norm_add_le (a * (1 - (t : ℂ)^m)) ((t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ)))
  
  have h_term1 : ‖a * (1 - (t : ℂ)^m)‖ = ‖a‖ * (1 - t^m) := by
    rw [norm_mul]
    have : 1 - (t : ℂ)^m = ((1 - t^m : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    have ht_m_le_one : t^m ≤ 1 := pow_le_one₀ ht_pos.le ht_le_one
    rw [abs_of_nonneg (by linarith)]
  
  have h_term2 : ‖(t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ))‖ = t^(m+1) * ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ := by
    rw [norm_mul, ht_m1_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    
  have h_M_bound : ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ ≤ M := by
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht_pos.le, ht_le_one⟩
    exact h_max ht_Icc
    
  have h_term2_le : t^(m+1) * ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ ≤ t^(m+1) * M := by
    gcongr
    
  calc ‖a * (1 - (t : ℂ)^m) + (t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ))‖
    _ ≤ ‖a * (1 - (t : ℂ)^m)‖ + ‖(t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ))‖ := h_triangle
    _ = ‖a‖ * (1 - t^m) + t^(m+1) * ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ := by rw [h_term1, h_term2]
    _ ≤ ‖a‖ * (1 - t^m) + t^(m+1) * M := by linarith [h_term2_le]
    _ = ‖a‖ - t^m * (‖a‖ - M * t) := by ring
    _ < ‖a‖ := by
        have ht_m_pos : 0 < t^m := pow_pos ht_pos m
        have h_M_t : M * t ≤ ‖a‖ / 2 := by
          have h2 : (M * ‖a‖) / (2 * (M + 1)) ≤ ‖a‖ / 2 := by
            have hm1 : 0 < 2 * (M + 1) := by positivity
            have h2pos : (0 : ℝ) < 2 := by positivity
            rw [div_le_div_iff₀ hm1 h2pos]
            calc (M * ‖a‖) * 2
              _ ≤ (M * ‖a‖) * 2 + ‖a‖ * 2 := by
                  have ha_pos : 0 ≤ ‖a‖ * 2 := by positivity
                  exact le_add_of_nonneg_right ha_pos
              _ = ‖a‖ * (2 * (M + 1)) := by ring
          calc M * t
              ≤ M * (‖a‖ / (2 * (M + 1))) := mul_le_mul_of_nonneg_left ht_le_bound hM_nonneg
            _ = (M * ‖a‖) / (2 * (M + 1)) := mul_div_assoc' M ‖a‖ _
            _ ≤ ‖a‖ / 2 := h2
        have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
        have h_diff : 0 < ‖a‖ - M * t := by linarith
        have h_prod : 0 < t^m * (‖a‖ - M * t) := mul_pos ht_m_pos h_diff
        exact sub_lt_self ‖a‖ h_prod

set_option maxHeartbeats 800000 in
/--
Chapter 19 local decrease: using the first nonzero coefficient of the
shifted polynomial, produce `w` with `‖p.eval (w + z₀)‖ < ‖p.eval z₀‖`.
-/
theorem shiftedPolynomial_local_norm_decrease
    (p : ℂ[X]) (z₀ : ℂ) (m : ℕ)
    (hp0 : p.eval z₀ ≠ 0)
    (hm0 : 0 < m)
    (hbelow :
      ∀ k, 0 < k → k < m →
        (shiftedPolynomial p z₀ - C (p.eval z₀)).coeff k = 0)
    (hm :
      (shiftedPolynomial p z₀ - C (p.eval z₀)).coeff m ≠ 0) :
    ∃ w : ℂ, ‖p.eval (w + z₀)‖ < ‖p.eval z₀‖ := by
  let r := shiftedPolynomial p z₀
  let a := p.eval z₀
  let c := (r - C a).coeff m
  have hconst : r.coeff 0 = a :=
    shiftedPolynomial_coeff_zero p z₀
  have hbelow_r : ∀ k, 0 < k → k < m → r.coeff k = 0 := by
    intro k hk0 hkm
    have := hbelow k hk0 hkm
    rwa [Polynomial.coeff_sub, Polynomial.coeff_C_ne_zero hk0.ne', sub_zero] at this
  have hm_r : r.coeff m = c := by
    have hmC : (C a : ℂ[X]).coeff m = 0 :=
      Polynomial.coeff_C_ne_zero hm0.ne'
    simp only [c, Polynomial.coeff_sub, hmC, sub_zero]
  obtain ⟨w, hw⟩ :=
    complex_poly_local_norm_decrease r a c m hm0 hp0 (by simpa [c] using hm) hconst hbelow_r hm_r
  refine ⟨w, ?_⟩
  rw [← shiftedPolynomial_eval]
  exact hw

set_option maxHeartbeats 3200000 in
/--
The minimum-modulus proof of FTA.
-/
theorem fta_minimum_modulus_contradiction
    (p : ℂ[X]) (z₀ : ℂ) (_hdeg : 1 ≤ p.natDegree)
    (hp0 : p.eval z₀ ≠ 0)
    (hmin : ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖)
    (hne : shiftedPolynomial p z₀ - C (p.eval z₀) ≠ 0) : False := by
  have hne' : shiftedPolynomial p z₀ - C ((shiftedPolynomial p z₀).eval 0) ≠ 0 := by
    rwa [shiftedPolynomial_eval_zero]
  obtain ⟨m, hm0, hm_ne, hm_below⟩ :=
    exists_first_nonzero_coeff_of_sub_C_eval_zero_ne_zero hne'
  rw [shiftedPolynomial_eval_zero] at hm_ne hm_below
  obtain ⟨w, hw⟩ :=
    shiftedPolynomial_local_norm_decrease p z₀ m hp0 hm0 (fun k hk0 hkm => hm_below k hkm) hm_ne
  exact absurd (hmin (w + z₀)) (not_le.mpr hw)



lemma exists_min_norm (p : ℂ[X]) :
    ∃ z₀ : ℂ, ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖ :=
  Polynomial.exists_forall_norm_le p



end ProofsInTheBook.Chapter19

open Polynomial Bornology
open ProofsInTheBook.Chapter19

theorem solution (p : ℂ[X]) (hdeg : 1 ≤ p.natDegree) : ∃ z : ℂ, p.eval z = 0 := by
  obtain ⟨z₀, hmin⟩ := exists_min_norm p
  by_contra h
  push Not at h
  have hp0 : p.eval z₀ ≠ 0 := h z₀
  have hne : shiftedPolynomial p z₀ - C (p.eval z₀) ≠ 0 := by
    intro hc
    have h_deg1 : p.natDegree = (shiftedPolynomial p z₀).natDegree := by
      have : shiftedPolynomial p z₀ = p.comp (X + C z₀) := rfl
      rw [this, natDegree_comp, natDegree_X_add_C, mul_one]
    have h_deg2 : (shiftedPolynomial p z₀).natDegree = 0 := by
      have h_eq : shiftedPolynomial p z₀ = C (p.eval z₀) := eq_of_sub_eq_zero hc
      rw [h_eq]
      exact natDegree_C (p.eval z₀)
    omega
  exact fta_minimum_modulus_contradiction p z₀ hdeg hp0 hmin hne
