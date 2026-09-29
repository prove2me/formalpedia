-- Prove2me | solution 1 for bernoulli_nonnegative_statistic_moment_from_scaled_large_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-21T21:53:04.421979+00:00
-- url     : https://prove2.me/submissions/1ddc05f3-c884-415d-8ec7-aecad1809ecd

import Mathlib
import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open Finset MeasureTheory
open scoped Classical BigOperators

private lemma pow_eq_integral (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (hx : 0 ≤ x) :
    x ^ q = ∫ t in Set.Ioi (0:ℝ), (if t < x then (q:ℝ) * t ^ (q-1) else 0) := by
  have hrw : (∫ t in Set.Ioi (0:ℝ), (if t < x then (q:ℝ) * t ^ (q-1) else 0))
      = ∫ t in Set.Ioo (0:ℝ) x, (q:ℝ) * t ^ (q-1) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
        ← MeasureTheory.integral_indicator measurableSet_Ioo]
    congr 1; ext t
    simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Ioo]
    by_cases ht0 : (0:ℝ) < t <;> simp [ht0]
  rw [hrw]
  have hIoo : (∫ t in Set.Ioo (0:ℝ) x, (q:ℝ) * t ^ (q-1))
      = ∫ t in (0:ℝ)..x, (q:ℝ) * t ^ (q-1) := by
    rw [intervalIntegral.integral_of_le hx, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIoo, intervalIntegral.integral_const_mul, integral_pow, Nat.sub_add_cancel hq]
  have hc : ((q - 1 : ℕ) : ℝ) + 1 = (q:ℝ) := by rw [Nat.cast_sub hq]; push_cast; ring
  rw [hc, zero_pow (show q ≠ 0 by omega), sub_zero]
  have hqne : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

private lemma integrable_summand (q : ℕ) (W x : ℝ) :
    IntegrableOn (fun t => W * (if t < x then (q:ℝ) * t ^ (q-1) else 0)) (Set.Ioi (0:ℝ)) := by
  have heq : (fun t => W * (if t < x then (q:ℝ) * t ^ (q-1) else 0))
      = Set.indicator (Set.Iio x) (fun t => W * ((q:ℝ) * t ^ (q-1))) := by
    funext t; by_cases h : t < x <;> simp [h]
  rw [heq, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio x ∩ Set.Ioi (0:ℝ) = Set.Ioo 0 x := by
    ext t; simp [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, and_comm]
  rw [hset]
  exact ((continuous_const.mul (continuous_const.mul (continuous_pow _))).integrableOn_Icc).mono_set
    Set.Ioo_subset_Icc_self

private lemma gamma_tail (q : ℕ) (hq : 1 ≤ q) (Cdev : ℝ) (hC : 0 < Cdev) :
    ∫ t in Set.Ioi (0:ℝ), t ^ (q-1) * Real.exp (-(t / Cdev))
      = Cdev ^ q * (Nat.factorial (q-1) : ℝ) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hr : (0:ℝ) < 1 / Cdev := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (q:ℝ)) (r := 1 / Cdev) hq0 hr
  have hcongr : (∫ t in Set.Ioi (0:ℝ), t ^ ((q:ℝ) - 1) * Real.exp (-(1 / Cdev * t)))
      = ∫ t in Set.Ioi (0:ℝ), t ^ (q-1) * Real.exp (-(t / Cdev)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show t ^ ((q:ℝ) - 1) * Real.exp (-(1 / Cdev * t)) = t ^ (q - 1) * Real.exp (-(t / Cdev))
    have h1 : t ^ ((q:ℝ) - 1) = t ^ (q - 1) := by
      rw [← Real.rpow_natCast t (q-1), Nat.cast_sub hq, Nat.cast_one]
    have h2 : (1 / Cdev * t) = t / Cdev := by ring
    rw [h1, h2]
  rw [hcongr] at key
  rw [key]
  have hCdev : (1 : ℝ) / (1 / Cdev) = Cdev := by field_simp
  rw [hCdev]
  have hrpow : Cdev ^ ((q:ℝ)) = Cdev ^ q := by rw [← Real.rpow_natCast Cdev q]
  rw [hrpow]; congr 1
  have hg : Real.Gamma ((q:ℝ)) = Real.Gamma (((q-1:ℕ):ℝ) + 1) := by
    congr 1; rw [Nat.cast_sub hq, Nat.cast_one]; ring
  rw [hg, Real.Gamma_nat_eq_factorial]

private lemma gamma_integrand_integrable (q : ℕ) (hq : 1 ≤ q) (Cdev : ℝ) (hC : 0 < Cdev) :
    IntegrableOn (fun t => t ^ (q-1) * Real.exp (-(t / Cdev))) (Set.Ioi (0:ℝ)) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := ((q:ℝ)-1)) (p := (1:ℝ)) (b := 1/Cdev)
    (by have : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
        linarith) le_rfl (by positivity)
  apply hb.congr
  apply Filter.EventuallyEq.symm
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.Ioi 0, self_mem_ae_restrict measurableSet_Ioi, ?_⟩
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  show t ^ (q-1) * Real.exp (-(t / Cdev)) = t ^ ((q:ℝ)-1) * Real.exp (-(1/Cdev) * t ^ (1:ℝ))
  have h1 : t ^ (q-1) = t ^ ((q:ℝ)-1) := by
    rw [← Real.rpow_natCast t (q-1), Nat.cast_sub hq, Nat.cast_one]
  rw [h1, Real.rpow_one, show -(t/Cdev) = -(1/Cdev) * t from by ring]

-- the swap
private lemma exp_eq_integral {n₁ n₂ : ℕ} (p : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Ω, 0 ≤ F Ω) :
    bernoulliExpectation p (fun Ω => F Ω ^ q)
      = ∫ t in Set.Ioi (0:ℝ), (q:ℝ) * t ^ (q-1)
            * bernoulliEventProb p (fun Ω => t < F Ω) := by
  unfold bernoulliExpectation bernoulliEventProb
  have hstep1 : (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω * F Ω ^ q)
      = ∑ Ω : Finset (Fin n₁ × Fin n₂),
          ∫ t in Set.Ioi (0:ℝ),
            bernoulliObservationWeight p Ω * (if t < F Ω then (q:ℝ) * t ^ (q-1) else 0) := by
    apply Finset.sum_congr rfl
    intro Ω _
    rw [pow_eq_integral q hq (F Ω) (hF Ω), ← MeasureTheory.integral_const_mul]
  rw [hstep1, ← MeasureTheory.integral_finsetSum _
        (fun Ω _ => integrable_summand q (bernoulliObservationWeight p Ω) (F Ω))]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  show (∑ Ω : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Ω * (if t < F Ω then (q:ℝ) * t ^ (q-1) else 0))
      = (q:ℝ) * t ^ (q-1)
          * ∑ Ω : Finset (Fin n₁ × Fin n₂),
              (if t < F Ω then bernoulliObservationWeight p Ω else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Ω _
  by_cases h : t < F Ω <;> simp [h] <;> ring

private lemma integral_le (q : ℕ) (hq : 1 ≤ q) (Cdev : ℝ) (hC : 0 < Cdev)
    (μ : ℝ) (hμ : 0 < μ) (K : ℝ) (hK : 0 ≤ K) (P : ℝ → ℝ)
    (hP_int : IntegrableOn (fun t => (q:ℝ) * t ^ (q-1) * P t) (Set.Ioi 0))
    (hP1 : ∀ t, P t ≤ 1)
    (hPtail : ∀ t, 2 * μ ≤ t → P t ≤ K * Real.exp (-(t / Cdev))) :
    ∫ t in Set.Ioi (0:ℝ), (q:ℝ) * t ^ (q-1) * P t
      ≤ (2 * μ) ^ q + K * Cdev ^ q * (Nat.factorial q : ℝ) := by
  set b1 : ℝ → ℝ := fun t => (if t < 2 * μ then (q:ℝ) * t ^ (q-1) else 0) with hb1def
  set b2 : ℝ → ℝ := fun t => ((q:ℝ) * K) * (t ^ (q-1) * Real.exp (-(t / Cdev))) with hb2def
  have hb1_int : IntegrableOn b1 (Set.Ioi 0) := by
    have := integrable_summand q 1 (2 * μ)
    apply this.congr
    apply Filter.EventuallyEq.symm
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.univ, Filter.univ_mem, fun t _ => by simp [hb1def, one_mul]⟩
  have hb2_int : IntegrableOn b2 (Set.Ioi 0) :=
    (gamma_integrand_integrable q hq Cdev hC).const_mul _
  have hbound : ∀ t ∈ Set.Ioi (0:ℝ), (q:ℝ) * t ^ (q-1) * P t ≤ b1 t + b2 t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have hqt : 0 ≤ (q:ℝ) * t ^ (q-1) := by positivity
    by_cases hc : t < 2 * μ
    · have hle : (q:ℝ) * t ^ (q-1) * P t ≤ (q:ℝ) * t ^ (q-1) * 1 :=
        mul_le_mul_of_nonneg_left (hP1 t) hqt
      simp only [hb1def, hb2def, if_pos hc]
      have hb2nn : 0 ≤ ((q:ℝ) * K) * (t ^ (q-1) * Real.exp (-(t / Cdev))) := by positivity
      nlinarith [hle]
    · push_neg at hc
      have hPt : P t ≤ K * Real.exp (-(t / Cdev)) := hPtail t hc
      simp only [hb1def, hb2def, if_neg (not_lt.mpr hc)]
      have hle : (q:ℝ) * t ^ (q-1) * P t ≤ (q:ℝ) * t ^ (q-1) * (K * Real.exp (-(t / Cdev))) :=
        mul_le_mul_of_nonneg_left hPt hqt
      nlinarith [hle]
  calc ∫ t in Set.Ioi (0:ℝ), (q:ℝ) * t ^ (q-1) * P t
      ≤ ∫ t in Set.Ioi (0:ℝ), (b1 t + b2 t) :=
        setIntegral_mono_on hP_int (hb1_int.add hb2_int) measurableSet_Ioi hbound
    _ = (∫ t in Set.Ioi (0:ℝ), b1 t) + ∫ t in Set.Ioi (0:ℝ), b2 t :=
        integral_add hb1_int hb2_int
    _ = (2 * μ) ^ q + K * Cdev ^ q * (Nat.factorial q : ℝ) := by
        have e1 : (∫ t in Set.Ioi (0:ℝ), b1 t) = (2 * μ) ^ q := by
          rw [hb1def]; exact (pow_eq_integral q hq (2 * μ) (by positivity)).symm
        have e2 : (∫ t in Set.Ioi (0:ℝ), b2 t) = K * Cdev ^ q * (Nat.factorial q : ℝ) := by
          rw [hb2def, MeasureTheory.integral_const_mul, gamma_tail q hq Cdev hC]
          have hfac : (q:ℝ) * (Nat.factorial (q-1) : ℝ) = (Nat.factorial q : ℝ) := by
            rw [← Nat.cast_mul, Nat.mul_factorial_pred (by omega)]
          ring_nf
          rw [← hfac]; ring
        rw [e1, e2]

private lemma total_prob {n₁ n₂ : ℕ} (p : ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω) = 1 := by
  unfold bernoulliObservationWeight
  have key : (∏ _c : Fin n₁ × Fin n₂, (p + (1 - p)))
      = ∑ Ω : Finset (Fin n₁ × Fin n₂), (∏ _c ∈ Ω, p) * ∏ _c ∈ univ \ Ω, (1 - p) := by
    rw [Finset.prod_add, Finset.powerset_univ]
  have hone : (∏ _c : Fin n₁ × Fin n₂, (p + (1 - p))) = 1 := by
    rw [Finset.prod_congr rfl (fun c _ => show p + (1 - p) = 1 by ring), Finset.prod_const_one]
  have hsum : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
      = ∑ Ω : Finset (Fin n₁ × Fin n₂), (∏ _c ∈ Ω, p) * ∏ _c ∈ univ \ Ω, (1 - p) := by
    apply Finset.sum_congr rfl
    intro Ω _
    rw [Finset.prod_const, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  rw [hsum, ← key]; exact hone

theorem solution
    (Cdev : ℝ) :
    0 < Cdev →
    ∃ Cmoment : ℝ, 0 < Cmoment ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        1 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        (q : ℝ) ≤
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂)) →
        ∀ F : Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ Omega : Finset (Fin n₁ × Fin n₂), 0 ≤ F Omega) →
        (∀ lambda : ℝ, 2 ≤ lambda →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂))) <
                  F Omega) ≤
            (↑(max n₁ n₂)) *
              Real.exp
                (-(lambda *
                    (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                      (↑(max n₁ n₂)))) / Cdev)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega : Finset (Fin n₁ × Fin n₂) => F Omega ^ q) ≤
          (Cmoment * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (↑(max n₁ n₂))) ^ q := by
  intro hCdev
  refine ⟨2 + Real.exp (1/2) * Cdev, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q hn1 hn2 hm hq hqlog hqmu F hF hLD
  have hN0 : 0 < ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  set p := ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hpdef
  set K := max n₁ n₂ with hKdef
  have hp0 : 0 ≤ p := by rw [hpdef]; positivity
  have hp1 : p ≤ 1 := by
    rw [hpdef, div_le_one hN0]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this ⊢; linarith
  have hWnn : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Ω := by
    intro Ω; unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  have hKpos : 0 < K := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hKR1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
  have hKRpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  set μ := p * (K : ℝ) with hμdef
  have hμpos : 0 < μ := by
    have h1q : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [hμdef]; linarith [le_trans h1q hqmu]
  rw [exp_eq_integral p q hq F hF]
  -- bound the integral
  refine le_trans (integral_le q hq Cdev hCdev μ hμpos (K : ℝ) (le_of_lt hKRpos)
      (fun t => bernoulliEventProb p (fun Ω => t < F Ω)) ?hint ?h1 ?htail) ?final
  case hint =>
    have heqf : (fun t => (q:ℝ) * t ^ (q-1) * bernoulliEventProb p (fun Ω => t < F Ω))
        = fun t => ∑ Ω : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Ω * (if t < F Ω then (q:ℝ) * t ^ (q-1) else 0) := by
      funext t
      unfold bernoulliEventProb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Ω _
      by_cases h : t < F Ω <;> simp [h] <;> ring
    rw [heqf]
    exact MeasureTheory.integrable_finsetSum _
      (fun Ω _ => integrable_summand q (bernoulliObservationWeight p Ω) (F Ω))
  case h1 =>
    intro t
    unfold bernoulliEventProb
    calc (∑ Ω : Finset (Fin n₁ × Fin n₂),
            if t < F Ω then bernoulliObservationWeight p Ω else 0)
        ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω := by
          apply Finset.sum_le_sum
          intro Ω _
          by_cases h : t < F Ω
          · rw [if_pos h]
          · rw [if_neg h]; exact hWnn Ω
      _ = 1 := total_prob p
  case htail =>
    intro t ht
    have hlam : (2 : ℝ) ≤ t / μ := by rw [le_div_iff₀ hμpos]; linarith
    have hev : (t / μ) * (p * (K : ℝ)) = t := by rw [← hμdef]; field_simp
    have hkey := hLD (t / μ) hlam
    rw [hev] at hkey
    rw [show -(t) / Cdev = -(t / Cdev) from by rw [neg_div]] at hkey
    exact hkey
  case final =>
    -- (2μ)^q + K Cdev^q q! ≤ ((2 + exp(1/2) Cdev) p K)^q
    have hμeq : μ = p * (K : ℝ) := hμdef
    -- K ≤ exp(q/2)
    have hlogK : Real.log (K : ℝ) ≤ (q : ℝ) / 2 := by
      have hlognn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR1
      have h2 : 2 * Real.log (K : ℝ) ≤ β * Real.log (K : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hβ) hlognn
      have : β * Real.log (K : ℝ) ≤ (q : ℝ) := hqlog
      linarith
    have hKexp : (K : ℝ) ≤ Real.exp ((q : ℝ) / 2) := by
      rw [← Real.exp_log hKRpos]
      exact Real.exp_le_exp.mpr hlogK
    -- q! ≤ μ^q
    have hfac : (Nat.factorial q : ℝ) ≤ μ ^ q := by
      have h1 : (Nat.factorial q : ℝ) ≤ (q : ℝ) ^ q := by
        exact_mod_cast Nat.factorial_le_pow q
      have h2 : (q : ℝ) ^ q ≤ μ ^ q :=
        pow_le_pow_left₀ (by positivity) hqmu q
      exact le_trans h1 h2
    -- term2 bound
    have hterm2 : (K : ℝ) * Cdev ^ q * (Nat.factorial q : ℝ)
        ≤ (Real.exp (1/2) * Cdev * μ) ^ q := by
      have hexpq : (Real.exp (1/2)) ^ q = Real.exp ((q : ℝ) / 2) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hμnn : 0 ≤ μ := le_of_lt hμpos
      have hCnn : 0 ≤ Cdev := le_of_lt hCdev
      have hmul : (K : ℝ) * (Nat.factorial q : ℝ) ≤ Real.exp ((q:ℝ)/2) * μ ^ q :=
        mul_le_mul hKexp hfac (by positivity) (by positivity)
      calc (K : ℝ) * Cdev ^ q * (Nat.factorial q : ℝ)
          = ((K : ℝ) * (Nat.factorial q : ℝ)) * Cdev ^ q := by ring
        _ ≤ (Real.exp ((q:ℝ)/2) * μ ^ q) * Cdev ^ q :=
            mul_le_mul_of_nonneg_right hmul (by positivity)
        _ = (Real.exp (1/2) * Cdev * μ) ^ q := by
            rw [mul_pow (Real.exp (1/2) * Cdev) μ, mul_pow (Real.exp (1/2)) Cdev, hexpq]; ring
    -- combine
    have hsum : (2 * μ) ^ q + (K : ℝ) * Cdev ^ q * (Nat.factorial q : ℝ)
        ≤ (2 * μ) ^ q + (Real.exp (1/2) * Cdev * μ) ^ q := by linarith
    have hadd : (2 * μ) ^ q + (Real.exp (1/2) * Cdev * μ) ^ q
        ≤ (2 * μ + Real.exp (1/2) * Cdev * μ) ^ q :=
      pow_add_pow_le (by positivity) (by positivity) (by omega)
    have hfinal : (2 * μ + Real.exp (1/2) * Cdev * μ) ^ q
        = ((2 + Real.exp (1/2) * Cdev) * p * (K : ℝ)) ^ q := by
      rw [hμeq]; ring
    calc (2 * μ) ^ q + (K : ℝ) * Cdev ^ q * (Nat.factorial q : ℝ)
        ≤ (2 * μ + Real.exp (1/2) * Cdev * μ) ^ q := le_trans hsum hadd
      _ = ((2 + Real.exp (1/2) * Cdev) * p * (K : ℝ)) ^ q := hfinal
