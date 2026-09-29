-- Prove2me | solution 1 for mme_dwz_paired_exact_typical_useful_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T14:59:54.882966+00:00
-- url     : https://prove2.me/submissions/89729668-d2ae-49cf-bf6b-c896100d60d1

import Theorems.Thm_mme_scaled_multinomial_log_rate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

open BigOperators Filter
open scoped Topology Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MME.DWZC1PairedTypicalRate

private noncomputable def entropyMass {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  (∑ i, x i) * Real.log (∑ i, x i) - ∑ i, x i * Real.log (x i)

private theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      y * (x * Real.log x) + x * (y * Real.log y) := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog] at h
  nlinarith

private theorem entropyMass_mul {I : Type*} [Fintype I]
    (x : I → ℝ) (b : ℝ) :
    entropyMass (fun i ↦ x i * b) = b * entropyMass x := by
  unfold entropyMass
  rw [← Finset.sum_mul, mul_log_mul]
  simp only [mul_log_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private theorem entropyMass_product {A B : Type*} [Fintype A] [Fintype B]
    (l : A → ℝ) (r : B → ℝ) :
    entropyMass (fun ab : A × B ↦ l ab.1 * r ab.2) =
      entropyMass (fun a ↦ l a * ∑ b, r b) +
        entropyMass (fun b ↦ (∑ a, l a) * r b) := by
  rw [entropyMass_mul]
  have hright : entropyMass (fun b ↦ (∑ a, l a) * r b) =
      (∑ a, l a) * entropyMass r := by
    simpa only [mul_comm] using entropyMass_mul r (∑ a, l a)
  rw [hright]
  unfold entropyMass
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_log_mul,
    Finset.sum_add_distrib]
  ring

theorem paired_log_gap_tendsto_zero
    {A B : Type*} [Fintype A] [Fintype B]
    (l : A → ℕ) (r : B → ℕ) (DL DR : ℕ)
    (hl : ∑ a, l a = DL) (hr : ∑ b, r b = DR) :
    Tendsto (fun t : ℕ ↦
      (Real.log (Nat.multinomial Finset.univ
          (fun ab : A × B ↦ t * l ab.1 * r ab.2) : ℝ) -
        Real.log (Nat.multinomial Finset.univ
          (fun a ↦ t * l a * DR) : ℝ) -
        Real.log (Nat.multinomial Finset.univ
          (fun b ↦ t * DL * r b) : ℝ)) / (t : ℝ))
      atTop (𝓝 0) := by
  have hj := mme_scaled_multinomial_log_rate (fun ab : A × B ↦ l ab.1 * r ab.2)
  have hleft := mme_scaled_multinomial_log_rate (fun a ↦ l a * DR)
  have hright := mme_scaled_multinomial_log_rate (fun b ↦ DL * r b)
  have h := (hj.sub hleft).sub hright
  have hmass := entropyMass_product (fun a ↦ (l a : ℝ)) (fun b ↦ (r b : ℝ))
  rw [← Nat.cast_sum, ← Nat.cast_sum, hl, hr] at hmass
  have hzero : entropyMass (fun ab : A × B ↦ (l ab.1 : ℝ) * r ab.2) -
      entropyMass (fun a ↦ (l a : ℝ) * DR) -
      entropyMass (fun b ↦ (DL : ℝ) * r b) = 0 := by linarith
  simp only [entropyMass, ← Nat.cast_mul, ← Nat.cast_sum] at hzero
  rw [hzero] at h
  convert h using 1
  funext t
  simp only [sub_div, mul_comm t, mul_assoc]

theorem paired_eventually_subexponential_fraction
    {A B : Type*} [Fintype A] [Fintype B]
    (l : A → ℕ) (r : B → ℕ) (DL DR : ℕ)
    (hl : ∑ a, l a = DL) (hr : ∑ b, r b = DR)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) *
        (Nat.multinomial Finset.univ (fun a ↦ t * l a * DR) : ℝ) *
        (Nat.multinomial Finset.univ (fun b ↦ t * DL * r b) : ℝ) ≤
      (Nat.multinomial Finset.univ
        (fun ab : A × B ↦ t * l ab.1 * r ab.2) : ℝ) := by
  have h := (paired_log_gap_tendsto_zero l r DL DR hl hr).eventually
    (lt_mem_nhds (neg_neg_of_pos heps))
  filter_upwards [h, eventually_gt_atTop 0] with t ht htpos
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hj : (0 : ℝ) < Nat.multinomial Finset.univ
      (fun ab : A × B ↦ t * l ab.1 * r ab.2) := by
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ)
      (f := fun ab : A × B ↦ t * l ab.1 * r ab.2)
  have hleft : (0 : ℝ) < Nat.multinomial Finset.univ (fun a ↦ t * l a * DR) := by
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ) (f := fun a ↦ t * l a * DR)
  have hright : (0 : ℝ) < Nat.multinomial Finset.univ (fun b ↦ t * DL * r b) := by
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ) (f := fun b ↦ t * DL * r b)
  have hlog := (lt_div_iff₀ htR).mp ht
  apply (Real.log_le_log_iff
    (mul_pos (mul_pos (Real.exp_pos _) hleft) hright) hj).mp
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hleft).ne' hright.ne',
    Real.log_mul (Real.exp_pos _).ne' hleft.ne', Real.log_exp]
  linarith

private theorem product_scaled_multinomial_rate
    {S I : Type*} [Fintype S] [Fintype I] (a : S → I → ℕ) :
    Tendsto (fun t : ℕ ↦ Real.log
      (∏ s, (Nat.multinomial Finset.univ (fun i ↦ a s i * t) : ℝ)) / (t : ℝ))
      atTop (𝓝 (∑ s, entropyMass (fun i ↦ (a s i : ℝ)))) := by
  have h := tendsto_finset_sum Finset.univ
    (fun s _ ↦ mme_scaled_multinomial_log_rate (a s))
  simp only [entropyMass, ← Nat.cast_sum] at *
  convert h using 1
  funext t
  rw [Real.log_prod]
  · exact Finset.sum_div ..
  · intro s _
    exact_mod_cast (Nat.multinomial_pos (s := Finset.univ)
      (f := fun i ↦ a s i * t)).ne'

private theorem paired_entropy_cancellation
    {S A : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) :
    (∑ s, entropyMass (fun ab : A × A ↦
      (k s : ℝ) * p s ab.1 * p (sigma s) ab.2)) =
    ∑ s, entropyMass (fun a ↦ (D : ℝ) * (k s + k (sigma s)) * p s a) := by
  let H (s : S) : ℝ := entropyMass (fun a ↦ (p s a : ℝ))
  have hsum (s : S) : ∑ a, (p s a : ℝ) = D := by exact_mod_cast hp s
  have hj (s : S) : entropyMass (fun ab : A × A ↦
      (k s : ℝ) * p s ab.1 * p (sigma s) ab.2) =
      (k s : ℝ) * ((D : ℝ) * H s + (D : ℝ) * H (sigma s)) := by
    have hfun : (fun ab : A × A ↦ (k s : ℝ) * p s ab.1 * p (sigma s) ab.2) =
        (fun ab : A × A ↦ ((p s ab.1 : ℝ) * p (sigma s) ab.2) * k s) := by
      funext ab
      ring
    rw [hfun, entropyMass_mul,
      entropyMass_product (fun a ↦ (p s a : ℝ)) (fun b ↦ (p (sigma s) b : ℝ)),
      hsum, hsum,
      entropyMass_mul]
    have hrev : entropyMass (fun b ↦ (D : ℝ) * p (sigma s) b) =
        (D : ℝ) * H (sigma s) := by
      simpa only [mul_comm] using entropyMass_mul (fun b ↦ (p (sigma s) b : ℝ)) (D : ℝ)
    rw [hrev]
  have hu (s : S) : entropyMass (fun a ↦
      (D : ℝ) * (k s + k (sigma s)) * p s a) =
      (D : ℝ) * (k s + k (sigma s)) * H s := by
    simpa only [mul_comm] using entropyMass_mul
      (fun a ↦ (p s a : ℝ)) ((D : ℝ) * (k s + k (sigma s)))
  have hreindex : (∑ s, (k s : ℝ) * H (sigma s)) =
      ∑ s, (k (sigma s) : ℝ) * H s := by
    simpa only [hsigma] using sigma.sum_comp
      (fun s ↦ (k (sigma s) : ℝ) * H s)
  simp_rw [hj, hu]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp_rw [mul_left_comm (k _ : ℝ) (D : ℝ)]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hreindex]
  simp only [mul_assoc, ← Finset.mul_sum]

/-- The exact independent paired types and all merged child-useful types
have the same exponential count rate. This includes zero weights/profiles. -/
theorem joint_useful_log_gap_tendsto_zero
    {S A : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) :
    Tendsto (fun t : ℕ ↦
      (Real.log (∏ s, (Nat.multinomial Finset.univ
          (fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2) : ℝ)) -
        Real.log (∏ s, (Nat.multinomial Finset.univ
          (fun a ↦ t * D * (k s + k (sigma s)) * p s a) : ℝ))) / (t : ℝ))
      atTop (𝓝 0) := by
  have hj := product_scaled_multinomial_rate
    (fun s (ab : A × A) ↦ k s * p s ab.1 * p (sigma s) ab.2)
  have hu := product_scaled_multinomial_rate
    (fun s a ↦ D * (k s + k (sigma s)) * p s a)
  have h := hj.sub hu
  have hmass := paired_entropy_cancellation sigma hsigma p D hp k
  simp only [Nat.cast_mul, Nat.cast_add] at h
  rw [hmass, sub_self] at h
  convert h using 1
  funext t
  simp only [sub_div, mul_comm t, mul_assoc]

theorem joint_eventually_subexponential_useful_fraction
    {S A : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) *
        (∏ s, (Nat.multinomial Finset.univ
          (fun a ↦ t * D * (k s + k (sigma s)) * p s a) : ℝ)) ≤
      (∏ s, (Nat.multinomial Finset.univ
        (fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2) : ℝ)) := by
  have h := (joint_useful_log_gap_tendsto_zero sigma hsigma p D hp k).eventually
    (lt_mem_nhds (neg_neg_of_pos heps))
  filter_upwards [h, eventually_gt_atTop 0] with t ht htpos
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hj : (0 : ℝ) < ∏ s, (Nat.multinomial Finset.univ
      (fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2) : ℝ) := by
    apply Finset.prod_pos
    intro s _
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ)
      (f := fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2)
  have hu : (0 : ℝ) < ∏ s, (Nat.multinomial Finset.univ
      (fun a ↦ t * D * (k s + k (sigma s)) * p s a) : ℝ) := by
    apply Finset.prod_pos
    intro s _
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ)
      (f := fun a ↦ t * D * (k s + k (sigma s)) * p s a)
  have hlog := (lt_div_iff₀ htR).mp ht
  apply (Real.log_le_log_iff (mul_pos (Real.exp_pos _) hu) hj).mp
  rw [Real.log_mul (Real.exp_pos _).ne' hu.ne', Real.log_exp]
  linarith

end MME.DWZC1PairedTypicalRate

theorem solution
    {S A : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) :
    let J : ℕ → ℝ := fun t ↦ ∏ s, (Nat.multinomial Finset.univ
      (fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2) : ℝ)
    let U : ℕ → ℝ := fun t ↦ ∏ s, (Nat.multinomial Finset.univ
      (fun a ↦ t * D * (k s + k (sigma s)) * p s a) : ℝ)
    Tendsto (fun t : ℕ ↦ (Real.log (J t) - Real.log (U t)) / (t : ℝ))
      atTop (𝓝 0) ∧
    ∀ eps : ℝ, 0 < eps → ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) * U t ≤ J t := by
  dsimp only
  exact ⟨MME.DWZC1PairedTypicalRate.joint_useful_log_gap_tendsto_zero
    sigma hsigma p D hp k,
    MME.DWZC1PairedTypicalRate.joint_eventually_subexponential_useful_fraction
    sigma hsigma p D hp k⟩

