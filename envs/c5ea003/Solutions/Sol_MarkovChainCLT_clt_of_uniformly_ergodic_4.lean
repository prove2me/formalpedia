-- Prove2me | solution 4 for MarkovChainCLT.clt_of_uniformly_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:40:18.151661+00:00
-- url     : https://prove2.me/submissions/50e0ef7f-76b9-40f4-8413-a42d7b73c66b

import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_stationary_clt_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_clt_of_bounded_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_integral_sq_scaled_sampleAvg_le
import Theorems.Thm_MarkovChainCLT_integrable_sq_scaled_sampleAvg
import Theorems.Thm_MarkovChainCLT_gaussian_variance_le_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_abs_exp_variance_sub_le_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_abs_sub_le_exp_mul_abs_exp_neg_half_sub
import Theorems.Thm_MarkovChainCLT_tendstoInDistribution_gaussian_of_L1_approx
import Theorems.Thm_MeasureTheory_tendsto_integral_sq_sub_truncation
import Theorems.Thm_ProbabilityTheory_integrable_of_integrable_sq
import Theorems.Thm_ProbabilityTheory_integral_abs_le_sqrt_integral_sq
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option maxHeartbeats 4000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (huni : MarkovChainCLT.UniformlyErgodic P π) (hL2 : MemLp f 2 π) :
    MarkovChainCLT.SatisfiesCLT P π f := by
  classical
  have hinv : Kernel.Invariant P π := hP.1
  have hfsq : Integrable (fun x => (f x) ^ 2) π := hL2.integrable_sq
  have hfint : Integrable f π := ProbabilityTheory.integrable_of_integrable_sq π f hf hfsq
  obtain ⟨N, hN, hrate⟩ := MarkovChainCLT.exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  -- ## the clipping map and its two elementary properties
  set fK : ℕ → X → ℝ := fun K x => max (min (f x) (K : ℝ)) (-(K : ℝ)) with hfKdef
  have hclip : ∀ (y K : ℝ), 0 ≤ K →
      |max (min y K) (-K)| ≤ |y| ∧ |y - max (min y K) (-K)| ≤ |y| := by
    intro y K hK
    rcases le_total y K with h1 | h1
    · rcases le_total (-K) y with h2 | h2
      · rw [min_eq_left h1, max_eq_left h2]
        exact ⟨le_refl _, by simp⟩
      · rw [min_eq_left h1, max_eq_right h2]
        constructor
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
    · rw [min_eq_right h1, max_eq_left (by linarith)]
      constructor
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
  have hfKm : ∀ K, Measurable (fK K) := fun K =>
    (hf.min measurable_const).max measurable_const
  have hfKb : ∀ K x, |fK K x| ≤ (K : ℝ) := by
    intro K x
    rw [abs_le]
    refine ⟨le_max_right _ _, max_le (min_le_right _ _) ?_⟩
    exact neg_le_self (Nat.cast_nonneg K)
  set rK : ℕ → X → ℝ := fun K x => f x - fK K x with hrKdef
  have hrKm : ∀ K, Measurable (rK K) := fun K => hf.sub (hfKm K)
  -- ## square integrability of the truncations and the tails
  have hdomsq : ∀ (g : X → ℝ), Measurable g → (∀ x, |g x| ≤ |f x|) →
      Integrable (fun x => (g x) ^ 2) π := by
    intro g hgm hgb
    refine Integrable.mono hfsq ((hgm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    have h1 := hgb x
    nlinarith [abs_nonneg (g x), abs_nonneg (f x), sq_abs (g x), sq_abs (f x)]
  have hfKsq : ∀ K, Integrable (fun x => (fK K x) ^ 2) π := fun K =>
    hdomsq (fK K) (hfKm K) (fun x => (hclip (f x) (K : ℝ) (Nat.cast_nonneg K)).1)
  have hrKsq : ∀ K, Integrable (fun x => (rK K x) ^ 2) π := fun K =>
    hdomsq (rK K) (hrKm K) (fun x => (hclip (f x) (K : ℝ) (Nat.cast_nonneg K)).2)
  have hfKint : ∀ K, Integrable (fK K) π := fun K =>
    ProbabilityTheory.integrable_of_integrable_sq π _ (hfKm K) (hfKsq K)
  -- ## a variance is at most a second moment
  have hvarle : ∀ (g : X → ℝ), Measurable g → Integrable (fun x => (g x) ^ 2) π →
      ∫ x, (g x - ∫ y, g y ∂π) ^ 2 ∂π ≤ ∫ x, (g x) ^ 2 ∂π := by
    intro g hgm hgsq
    have hgint : Integrable g π := ProbabilityTheory.integrable_of_integrable_sq π g hgm hgsq
    set m : ℝ := ∫ y, g y ∂π with hm
    have h1 : ∫ x, (g x - m) ^ 2 ∂π = ∫ x, ((g x) ^ 2 - 2 * m * g x + m ^ 2) ∂π := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    have hA : Integrable (fun x => (g x) ^ 2 - 2 * m * g x) π :=
      hgsq.sub (hgint.const_mul _)
    have hC : Integrable (fun _ : X => m ^ 2) π := integrable_const _
    have e1 : ∫ x, ((g x) ^ 2 - 2 * m * g x + m ^ 2) ∂π
        = (∫ x, ((g x) ^ 2 - 2 * m * g x) ∂π) + ∫ _ : X, m ^ 2 ∂π := integral_add hA hC
    have e2 : ∫ x, ((g x) ^ 2 - 2 * m * g x) ∂π
        = (∫ x, (g x) ^ 2 ∂π) - ∫ x, 2 * m * g x ∂π :=
      integral_sub hgsq (hgint.const_mul _)
    have e3 : ∫ x, 2 * m * g x ∂π = 2 * m * m := by
      rw [integral_const_mul, ← hm]
    have e4 : ∫ _ : X, m ^ 2 ∂π = m ^ 2 := by simp
    rw [h1, e1, e2, e3, e4]
    nlinarith [sq_nonneg m]
  -- ## the CLT-scaled statistics
  set Y : ℕ → (ℕ → X) → ℝ :=
    fun n ω => Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π) with hYdef
  set W : ℕ → ℕ → (ℕ → X) → ℝ :=
    fun K n ω => Real.sqrt n * (MarkovChainCLT.sampleAvg (fK K) n ω - ∫ x, fK K x ∂π) with hWdef
  set D : ℕ → ℕ → (ℕ → X) → ℝ :=
    fun K n ω => Real.sqrt n * (MarkovChainCLT.sampleAvg (rK K) n ω - ∫ x, rK K x ∂π) with hDdef
  have hmeasfun : ∀ (g : X → ℝ), Measurable g → ∀ n : ℕ,
      Measurable (fun ω : ℕ → X =>
        Real.sqrt n * (MarkovChainCLT.sampleAvg g n ω - ∫ x, g x ∂π)) := by
    intro g hgm n
    have h1 : Measurable (fun ω : ℕ → X => ∑ i ∈ Finset.range n, g (ω (i + 1))) :=
      Finset.measurable_sum _ (fun i _ => hgm.comp (measurable_pi_apply (i + 1)))
    have h2 : Measurable (fun ω : ℕ → X => MarkovChainCLT.sampleAvg g n ω) := by
      simp only [MarkovChainCLT.sampleAvg]
      exact measurable_const.mul h1
    exact measurable_const.mul (h2.sub measurable_const)
  have hYm : ∀ n, Measurable (Y n) := fun n => hmeasfun f hf n
  have hWm : ∀ K n, Measurable (W K n) := fun K n => hmeasfun (fK K) (hfKm K) n
  have hDm : ∀ K n, Measurable (D K n) := fun K n => hmeasfun (rK K) (hrKm K) n
  -- the difference of the two statistics is the statistic of the difference
  have hYWD : ∀ K n ω, Y n ω - W K n ω = D K n ω := by
    intro K n ω
    have hs : MarkovChainCLT.sampleAvg f n ω - MarkovChainCLT.sampleAvg (fK K) n ω
        = MarkovChainCLT.sampleAvg (rK K) n ω := by
      simp only [MarkovChainCLT.sampleAvg, hrKdef]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hi : (∫ x, f x ∂π) - ∫ x, fK K x ∂π = ∫ x, rK K x ∂π := by
      rw [hrKdef]
      exact (integral_sub hfint (hfKint K)).symm
    simp only [hYdef, hWdef, hDdef]
    rw [← hs, ← hi]
    ring
  -- ## the bounded central limit theorem for each truncation
  have hcltK : ∀ K, MarkovChainCLT.SatisfiesCLT P π (fK K) := fun K =>
    MarkovChainCLT.clt_of_bounded_of_uniformlyErgodic P π hinv huni (fK K) (hfKm K)
      (K : ℝ) (hfKb K)
  choose vv hvv using hcltK
  have hWclt : ∀ K, TendstoInDistribution (W K) atTop (id : ℝ → ℝ)
      (fun _ => MarkovChainCLT.chainMeasure P π) (gaussianReal 0 (vv K)) := fun K => hvv K π
  -- ## second moments
  have hWsqint : ∀ K n, Integrable (fun ω => (W K n ω) ^ 2)
      (MarkovChainCLT.chainMeasure P π) := fun K n =>
    MarkovChainCLT.integrable_sq_scaled_sampleAvg P π hinv (fK K) (hfKm K) (hfKsq K) n
  have hDsqint : ∀ K n, Integrable (fun ω => (D K n ω) ^ 2)
      (MarkovChainCLT.chainMeasure P π) := fun K n =>
    MarkovChainCLT.integrable_sq_scaled_sampleAvg P π hinv (rK K) (hrKm K) (hrKsq K) n
  have hN0 : (0 : ℝ) ≤ 4 * N := by positivity
  set B : ℝ := 4 * N * ∫ x, (f x) ^ 2 ∂π with hBdef
  have hB0 : 0 ≤ B := by
    have : (0 : ℝ) ≤ ∫ x, (f x) ^ 2 ∂π := integral_nonneg (fun x => sq_nonneg _)
    positivity
  have hWsq : ∀ K n, ∫ ω, (W K n ω) ^ 2 ∂(MarkovChainCLT.chainMeasure P π) ≤ B := by
    intro K n
    have h1 := MarkovChainCLT.integral_sq_scaled_sampleAvg_le P π hinv N hN hrate
      (fK K) (hfKm K) (hfKsq K) n
    have h2 : ∫ x, (fK K x - ∫ y, fK K y ∂π) ^ 2 ∂π ≤ ∫ x, (fK K x) ^ 2 ∂π :=
      hvarle (fK K) (hfKm K) (hfKsq K)
    have h3 : ∫ x, (fK K x) ^ 2 ∂π ≤ ∫ x, (f x) ^ 2 ∂π := by
      refine integral_mono (hfKsq K) hfsq (fun x => ?_)
      have h := (hclip (f x) (K : ℝ) (Nat.cast_nonneg K)).1
      nlinarith [abs_nonneg (fK K x), abs_nonneg (f x), sq_abs (fK K x), sq_abs (f x)]
    calc ∫ ω, (W K n ω) ^ 2 ∂(MarkovChainCLT.chainMeasure P π)
        ≤ 4 * N * ∫ x, (fK K x - ∫ y, fK K y ∂π) ^ 2 ∂π := h1
      _ ≤ 4 * N * ∫ x, (f x) ^ 2 ∂π :=
          mul_le_mul_of_nonneg_left (le_trans h2 h3) hN0
  have hvvB : ∀ K, ((vv K : ℝ)) ≤ B := fun K =>
    MarkovChainCLT.gaussian_variance_le_of_tendstoInDistribution
      (MarkovChainCLT.chainMeasure P π) (W K) (vv K) B (hWm K) (hWclt K) (hWsqint K) (hWsq K)
  -- ## the uniform approximation error
  set δ : ℕ → ℝ := fun K => Real.sqrt (4 * N * ∫ x, (rK K x) ^ 2 ∂π) with hδdef
  have hδnn : ∀ K, 0 ≤ δ K := fun K => Real.sqrt_nonneg _
  have hDsq : ∀ K n, ∫ ω, (D K n ω) ^ 2 ∂(MarkovChainCLT.chainMeasure P π)
      ≤ 4 * N * ∫ x, (rK K x) ^ 2 ∂π := by
    intro K n
    have h1 := MarkovChainCLT.integral_sq_scaled_sampleAvg_le P π hinv N hN hrate
      (rK K) (hrKm K) (hrKsq K) n
    exact le_trans h1 (mul_le_mul_of_nonneg_left (hvarle (rK K) (hrKm K) (hrKsq K)) hN0)
  have hIsub : ∀ K n, Integrable (fun ω => Y n ω - W K n ω)
      (MarkovChainCLT.chainMeasure P π) := by
    intro K n
    have h := ProbabilityTheory.integrable_of_integrable_sq
      (MarkovChainCLT.chainMeasure P π) (D K n) (hDm K n) (hDsqint K n)
    exact h.congr (by filter_upwards with ω; rw [hYWD K n ω])
  have hIabs : ∀ K n, Integrable (fun ω => |Y n ω - W K n ω|)
      (MarkovChainCLT.chainMeasure P π) := fun K n => (hIsub K n).abs
  have hδbd : ∀ K n, ∫ ω, |Y n ω - W K n ω| ∂(MarkovChainCLT.chainMeasure P π) ≤ δ K := by
    intro K n
    have hcg : ∫ ω, |Y n ω - W K n ω| ∂(MarkovChainCLT.chainMeasure P π)
        = ∫ ω, |D K n ω| ∂(MarkovChainCLT.chainMeasure P π) := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [hYWD K n ω]
    rw [hcg]
    calc ∫ ω, |D K n ω| ∂(MarkovChainCLT.chainMeasure P π)
        ≤ Real.sqrt (∫ ω, (D K n ω) ^ 2 ∂(MarkovChainCLT.chainMeasure P π)) :=
          ProbabilityTheory.integral_abs_le_sqrt_integral_sq _ (D K n) (hDm K n) (hDsqint K n)
      _ ≤ δ K := Real.sqrt_le_sqrt (hDsq K n)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => ∫ x, (rK K x) ^ 2 ∂π) atTop (𝓝 0) :=
      MeasureTheory.tendsto_integral_sq_sub_truncation π f hf hfsq
    have h2 : Tendsto (fun K : ℕ => 4 * (N : ℝ) * ∫ x, (rK K x) ^ 2 ∂π) atTop (𝓝 0) := by
      simpa using h1.const_mul (4 * (N : ℝ))
    have h3 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h2
    simpa using h3
  -- ## the truncated variances form a Cauchy sequence
  have hcross : ∀ (K L n : ℕ),
      ∫ ω, |W K n ω - W L n ω| ∂(MarkovChainCLT.chainMeasure P π) ≤ δ K + δ L := by
    intro K L n
    have hint1 : Integrable (fun ω => |Y n ω - W K n ω| + |Y n ω - W L n ω|)
        (MarkovChainCLT.chainMeasure P π) := (hIabs K n).add (hIabs L n)
    have hintW : Integrable (fun ω => |W K n ω - W L n ω|)
        (MarkovChainCLT.chainMeasure P π) := by
      have h := ((hIsub L n).sub (hIsub K n)).abs
      refine h.congr ?_
      filter_upwards with ω
      simp only [Pi.sub_apply]
      congr 1
      ring
    have hmono : ∫ ω, |W K n ω - W L n ω| ∂(MarkovChainCLT.chainMeasure P π)
        ≤ ∫ ω, (|Y n ω - W K n ω| + |Y n ω - W L n ω|)
            ∂(MarkovChainCLT.chainMeasure P π) := by
      refine integral_mono hintW hint1 (fun ω => ?_)
      have h1 : W K n ω - W L n ω = -(Y n ω - W K n ω) + (Y n ω - W L n ω) := by ring
      rw [h1]
      calc |-(Y n ω - W K n ω) + (Y n ω - W L n ω)|
          ≤ |-(Y n ω - W K n ω)| + |Y n ω - W L n ω| := abs_add_le _ _
        _ = |Y n ω - W K n ω| + |Y n ω - W L n ω| := by rw [abs_neg]
    have hsplit : ∫ ω, (|Y n ω - W K n ω| + |Y n ω - W L n ω|)
        ∂(MarkovChainCLT.chainMeasure P π)
        = (∫ ω, |Y n ω - W K n ω| ∂(MarkovChainCLT.chainMeasure P π))
          + ∫ ω, |Y n ω - W L n ω| ∂(MarkovChainCLT.chainMeasure P π) :=
      integral_add (hIabs K n) (hIabs L n)
    rw [hsplit] at hmono
    linarith [hδbd K n, hδbd L n]
  have hexpcauchy : ∀ K L : ℕ,
      |Real.exp (-(vv K : ℝ) / 2) - Real.exp (-(vv L : ℝ) / 2)| ≤ δ K + δ L := by
    intro K L
    refine MarkovChainCLT.abs_exp_variance_sub_le_of_tendstoInDistribution
      (MarkovChainCLT.chainMeasure P π) (W K) (W L) (vv K) (vv L) (δ K + δ L)
      (hWm K) (hWm L) (hWclt K) (hWclt L) ?_ (fun n => hcross K L n)
    intro n
    have h := ((hIsub L n).sub (hIsub K n)).abs
    refine h.congr ?_
    filter_upwards with ω
    simp only [Pi.sub_apply]
    congr 1
    ring
  set c1 : ℝ := 2 * Real.exp (B / 2) with hc1def
  have hc1 : 0 < c1 := by positivity
  have hvvcauchy : ∀ K L : ℕ, |(vv K : ℝ) - (vv L : ℝ)| ≤ c1 * (δ K + δ L) := by
    intro K L
    have h1 := MarkovChainCLT.abs_sub_le_exp_mul_abs_exp_neg_half_sub B (vv K : ℝ) (vv L : ℝ)
      (vv K).coe_nonneg (vv L).coe_nonneg (hvvB K) (hvvB L)
    exact le_trans h1 (mul_le_mul_of_nonneg_left (hexpcauchy K L) (by positivity))
  have hcauchy : CauchySeq (fun K => ((vv K : ℝ))) := by
    rw [Metric.cauchySeq_iff]
    intro e he
    obtain ⟨K0, hK0⟩ := (Metric.tendsto_atTop.mp hδ0) (e / (4 * c1)) (by positivity)
    refine ⟨K0, fun m hm k hk => ?_⟩
    have hdm : δ m < e / (4 * c1) := by
      have h := hK0 m hm
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hδnn m)] at h
    have hdk : δ k < e / (4 * c1) := by
      have h := hK0 k hk
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hδnn k)] at h
    rw [Real.dist_eq]
    have h2 : c1 * (δ m + δ k) < c1 * (2 * (e / (4 * c1))) :=
      mul_lt_mul_of_pos_left (by linarith) hc1
    have h3 : c1 * (2 * (e / (4 * c1))) = e / 2 := by
      field_simp
      ring
    have h4 := hvvcauchy m k
    rw [h3] at h2
    linarith
  obtain ⟨c0, hc0⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hc0nn : 0 ≤ c0 :=
    ge_of_tendsto hc0 (Eventually.of_forall (fun K => (vv K).coe_nonneg))
  set c : ℝ≥0 := ⟨c0, hc0nn⟩ with hcdef
  have hvtend : Tendsto (fun K => ((vv K : ℝ))) atTop (𝓝 ((c : ℝ))) := hc0
  -- ## the approximation lemma delivers the stationary central limit theorem
  have hYclt : TendstoInDistribution Y atTop (id : ℝ → ℝ)
      (fun _ => MarkovChainCLT.chainMeasure P π) (gaussianReal 0 c) :=
    MarkovChainCLT.tendstoInDistribution_gaussian_of_L1_approx
      (MarkovChainCLT.chainMeasure P π) Y W vv c δ hYm hWclt hIabs hδbd hδ0 hvtend
  exact MarkovChainCLT.satisfiesCLT_of_stationary_clt_of_uniformlyErgodic P π huni f hf c hYclt
