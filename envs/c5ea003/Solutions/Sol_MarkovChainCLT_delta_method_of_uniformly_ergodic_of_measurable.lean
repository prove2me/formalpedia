-- Prove2me | solution 1 for MarkovChainCLT.delta_method_of_uniformly_ergodic_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-21T17:42:31.448606+00:00
-- url     : https://prove2.me/submissions/852f4901-b75a-45c3-829c-da8912903003

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Theorems.Thm_MarkovChainCLT_clt_asymptotic_variance_of_uniformly_ergodic
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_integral_sq_scaled_sampleAvg_le
import Theorems.Thm_MarkovChainCLT_integrable_sq_scaled_sampleAvg
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

/-- A continuous linear functional on a finite-dimensional coordinate space is the
corresponding finite linear combination. -/
lemma clm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (g' : (ι → ℝ) →L[ℝ] ℝ)
    (v : ι → ℝ) : g' v = ∑ p, v p * g' (Pi.single p 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsingle : Pi.single p (v p) = (v p) • (Pi.single p (1:ℝ)) := by
    funext q
    by_cases h : q = p <;> simp [Pi.single_apply, h]
  rw [hsingle, map_smul, smul_eq_mul, mul_comm]

lemma measurable_sampleAvg (f : X → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω : ℕ → X => sampleAvg f n ω) := by
  unfold sampleAvg
  exact (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply (i + 1))).const_mul _

/-- **Tightness.** The CLT-scaled coordinate deviations have second moments bounded
uniformly in the horizon. -/
lemma exists_tightness_bound (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π)
    {ι : Type*} [Fintype ι] (u : X → ι → ℝ) (hu : ∀ p, Measurable (fun x => u x p))
    (hL2 : ∀ p, MemLp (fun x => u x p) 2 π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∫ ω, (∑ p : ι, (Real.sqrt n *
          (sampleAvg (fun x => u x p) n ω - ∫ x, u x p ∂π)) ^ 2) ∂(chainMeasure P π) ≤ C := by
  classical
  obtain ⟨N, hN, hrate⟩ := exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  have hsq : ∀ p : ι, Integrable (fun x => (u x p) ^ 2) π := fun p =>
    (memLp_two_iff_integrable_sq (hu p).aestronglyMeasurable).1 (hL2 p)
  refine ⟨∑ p : ι, 4 * (N : ℝ) * ∫ x, (u x p - ∫ y, u y p ∂π) ^ 2 ∂π, ?_, fun n => ?_⟩
  · refine Finset.sum_nonneg fun p _ => ?_
    have : (0:ℝ) ≤ ∫ x, (u x p - ∫ y, u y p ∂π) ^ 2 ∂π := integral_nonneg fun x => sq_nonneg _
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    positivity
  · have hint : ∀ p : ι, Integrable (fun ω : ℕ → X =>
        (Real.sqrt n * (sampleAvg (fun x => u x p) n ω - ∫ x, u x p ∂π)) ^ 2)
        (chainMeasure P π) := fun p =>
      integrable_sq_scaled_sampleAvg P π hinv (fun x => u x p) (hu p) (hsq p) n
    rw [integral_finset_sum _ (fun p _ => hint p)]
    refine Finset.sum_le_sum fun p _ => ?_
    exact integral_sq_scaled_sampleAvg_le P π hinv N hN hrate (fun x => u x p) (hu p) (hsq p) n

/-- **Delta method for Markov chain statistics (Lemma EC.5), with the estimator
required to be measurable.** -/
theorem delta_method_aux (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hP : HarrisErgodic P π)
    (huni : UniformlyErgodic P π) {ι : Type*} [Fintype ι]
    (u : X → ι → ℝ) (hu : ∀ p, Measurable (fun x => u x p))
    (hL2 : ∀ p, MemLp (fun x => u x p) 2 π)
    (g : (ι → ℝ) → ℝ) (hgm : Measurable g) (g' : (ι → ℝ) →L[ℝ] ℝ)
    (hg : HasFDerivAt g g' (fun p => ∫ x, u x p ∂π)) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (g (fun p => sampleAvg (fun x => u x p) n ω)
          - g (fun p => ∫ x, u x p ∂π)))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π)
      (gaussianReal 0 (asymptoticVariance P π (fun x => g' (u x))).toNNReal) := by
  classical
  have hinv : Kernel.Invariant P π := hP.1
  set m : ι → ℝ := fun p => ∫ x, u x p ∂π with hm
  set c : ι → ℝ := fun p => g' (Pi.single p 1) with hc
  set h : X → ℝ := fun x => g' (u x) with hh
  have hlin : ∀ v : ι → ℝ, g' v = ∑ p, v p * c p := clm_eq_sum g'
  have hexp : ∀ x, h x = ∑ p : ι, c p * u x p := by
    intro x
    show g' (u x) = _
    rw [hlin (u x)]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hhmeas : Measurable h := by
    have e : h = fun x => ∑ p : ι, c p * u x p := funext hexp
    rw [e]
    exact Finset.measurable_sum _ fun p _ => (hu p).const_mul _
  have hhL2 : MemLp h 2 π := by
    have e : h = fun x => ∑ p : ι, c p * u x p := funext hexp
    rw [e]
    have := memLp_finset_sum (μ := π) (p := 2) (Finset.univ : Finset ι)
      (f := fun p x => c p * u x p) (fun p _ => (hL2 p).const_mul (c p))
    simpa using this
  have hmean : ∫ x, h x ∂π = g' m := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
    rw [integral_finset_sum _ (fun p _ => ((hL2 p).integrable (by norm_num)).const_mul (c p))]
    rw [hlin m]
    exact Finset.sum_congr rfl fun p _ => by rw [integral_const_mul, hm]; ring
  -- the vector of coordinate sample averages
  set V : ℕ → (ℕ → X) → (ι → ℝ) := fun n ω p => sampleAvg (fun x => u x p) n ω with hV
  have hVmeas : ∀ n : ℕ, Measurable (fun ω : ℕ → X => V n ω) := fun n =>
    measurable_pi_lambda _ fun p => measurable_sampleAvg _ (hu p) n
  have hVg : ∀ (n : ℕ) (ω : ℕ → X), sampleAvg h n ω = g' (V n ω) := by
    intro n ω
    have hveq : V n ω = (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, u (ω (i + 1)) := by
      funext p
      simp [hV, sampleAvg, Finset.sum_apply]
    rw [hveq, map_smul, map_sum, smul_eq_mul]
    rfl
  -- the CLT for the linearized observable
  have hclt := (clt_asymptotic_variance_of_uniformly_ergodic P π hP huni h hhmeas hhL2).2.2 π
  set μc : Measure (ℕ → X) := chainMeasure P π with hμc
  set Z : ℕ → (ℕ → X) → ℝ := fun n ω => Real.sqrt n * (sampleAvg h n ω - ∫ x, h x ∂π) with hZ
  set Y : ℕ → (ℕ → X) → ℝ := fun n ω =>
    Real.sqrt n * (g (V n ω) - g m) with hY
  have hZmeas : ∀ n, Measurable (Z n) := fun n =>
    ((measurable_sampleAvg h hhmeas n).sub measurable_const).const_mul _
  have hYmeas : ∀ n, Measurable (Y n) := fun n =>
    ((hgm.comp (hVmeas n)).sub measurable_const).const_mul _
  -- the remainder
  have hdiff : ∀ (n : ℕ) (ω : ℕ → X),
      Y n ω - Z n ω = Real.sqrt n * (g (V n ω) - g m - g' (V n ω - m)) := by
    intro n ω
    rw [hY, hZ]
    simp only
    rw [hVg n ω, hmean, map_sub]
    ring
  -- tightness
  obtain ⟨C, hC0, hCbound⟩ := exists_tightness_bound P π hinv huni u hu hL2
  set Q : ℕ → (ℕ → X) → ℝ := fun n ω => ∑ p : ι, (Real.sqrt n * (V n ω p - m p)) ^ 2 with hQ
  have hVmeas' : ∀ (n : ℕ) (p : ι), Measurable (fun ω : ℕ → X => V n ω p) := fun n p =>
    measurable_sampleAvg _ (hu p) n
  have hQnonneg : ∀ n ω, 0 ≤ Q n ω := fun n ω =>
    Finset.sum_nonneg fun p _ => sq_nonneg _
  have hQmeas : ∀ n, Measurable (Q n) := fun n =>
    Finset.measurable_sum _ fun p _ =>
      (((hVmeas' n p).sub measurable_const).const_mul _).pow_const 2
  have hQint : ∀ n, Integrable (Q n) μc := by
    intro n
    refine integrable_finset_sum _ fun p _ => ?_
    exact integrable_sq_scaled_sampleAvg P π hinv (fun x => u x p) (hu p)
      ((memLp_two_iff_integrable_sq (hu p).aestronglyMeasurable).1 (hL2 p)) n
  have hnorm_le : ∀ v : ι → ℝ, ‖v‖ ≤ Real.sqrt (∑ p : ι, (v p) ^ 2) := by
    intro v
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro p
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun q : ι => (v q) ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_univ p))
  -- the remainder vanishes in probability
  have htim : TendstoInMeasure μc (Y - Z) atTop 0 := by
    refine tendstoInMeasure_of_ne_top ?_
    intro εe hεe hεtop
    set ε : ℝ := εe.toReal with hεdef
    have hε : 0 < ε := ENNReal.toReal_pos hεe.ne' hεtop
    have hsetsub : ∀ n : ℕ, {ω | εe ≤ edist ((Y - Z) n ω) ((0 : (ℕ → X) → ℝ) ω)}
        ⊆ {ω | ε ≤ |Y n ω - Z n ω|} := by
      intro n ω hω
      simp only [Set.mem_setOf_eq, Pi.sub_apply, Pi.zero_apply, edist_dist, Real.dist_eq,
        sub_zero] at hω
      have h1 : εe.toReal ≤ (ENNReal.ofReal |Y n ω - Z n ω|).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
      rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h1
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨η₀, hη₀pos, hη₀le⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ ENNReal.ofReal η₀ ≤ η := by
      rcases eq_or_lt_of_le (le_top : η ≤ ⊤) with heq | hlt
      · exact ⟨1, one_pos, heq ▸ le_top⟩
      · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' hlt.ne, by rw [ENNReal.ofReal_toReal hlt.ne]⟩
    set t : ℝ := Real.sqrt (C / η₀) + 1 with ht
    have ht0 : 0 < t := by positivity
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    have htC : C / t ^ 2 ≤ η₀ := by
      rw [div_le_iff₀ ht2]
      have h1 : Real.sqrt (C / η₀) ^ 2 = C / η₀ :=
        Real.sq_sqrt (by positivity)
      have h2 : C / η₀ ≤ t ^ 2 := by
        rw [ht]; nlinarith [Real.sqrt_nonneg (C / η₀), h1]
      rw [div_le_iff₀ hη₀pos] at h2
      linarith
    set δ : ℝ := ε / (2 * t) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨r, hr0, hrball⟩ := Metric.eventually_nhds_iff.1 (hg.isLittleO.def hδ0)
    have hsubset : ∀ n : ℕ, 1 ≤ n → t ^ 2 / r ^ 2 ≤ (n:ℝ) →
        {ω | ε ≤ |Y n ω - Z n ω|} ⊆ {ω | t ^ 2 ≤ Q n ω} := by
      intro n hn1 hn ω hω
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_le] at hcon
      simp only [Set.mem_setOf_eq] at hω
      set w : ι → ℝ := fun p => Real.sqrt n * (V n ω p - m p) with hw
      have hwQ : ‖w‖ ≤ Real.sqrt (Q n ω) := hnorm_le w
      have hsq : Real.sqrt (Q n ω) < t := by
        have hlt := Real.sqrt_lt_sqrt (hQnonneg n ω) hcon
        rwa [Real.sqrt_sq ht0.le] at hlt
      have hwlt : ‖w‖ < t := lt_of_le_of_lt hwQ hsq
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
      have hweq : w = Real.sqrt n • (V n ω - m) := by
        funext p; simp [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hnormw : ‖w‖ = Real.sqrt n * ‖V n ω - m‖ := by
        rw [hweq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hsnr : t / r ≤ Real.sqrt n := by
        refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
        rw [div_pow]
        exact hn
      have hVm : ‖V n ω - m‖ < r := by
        have h1 : Real.sqrt n * ‖V n ω - m‖ < t := by rw [← hnormw]; exact hwlt
        have h2 : (t / r) * ‖V n ω - m‖ ≤ Real.sqrt n * ‖V n ω - m‖ :=
          mul_le_mul_of_nonneg_right hsnr (norm_nonneg _)
        have h3 : (t / r) * ‖V n ω - m‖ < t := lt_of_le_of_lt h2 h1
        rw [div_mul_eq_mul_div, div_lt_iff₀ hr0] at h3
        nlinarith [ht0, hr0]
      have hRb : ‖g (V n ω) - g m - g' (V n ω - m)‖ ≤ δ * ‖V n ω - m‖ := by
        have hb := hrball (y := V n ω) (by rwa [dist_eq_norm])
        simpa using hb
      have hYZ : |Y n ω - Z n ω| ≤ δ * ‖w‖ := by
        rw [hdiff n ω, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt n * |g (V n ω) - g m - g' (V n ω - m)|
            ≤ Real.sqrt n * (δ * ‖V n ω - m‖) := by
              refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
              rw [← Real.norm_eq_abs]; exact hRb
          _ = δ * (Real.sqrt n * ‖V n ω - m‖) := by ring
          _ = δ * ‖w‖ := by rw [hnormw]
      have hlt2 : δ * ‖w‖ < δ * t := mul_lt_mul_of_pos_left hwlt hδ0
      have hdt : δ * t = ε / 2 := by rw [hδ]; field_simp
      linarith [hω, hYZ, hlt2, hdt, hε]
    have hMk : ∀ n : ℕ, μc {ω | t ^ 2 ≤ Q n ω} ≤ ENNReal.ofReal η₀ := by
      intro n
      have hm1 : t ^ 2 * (μc.real {ω | t ^ 2 ≤ Q n ω}) ≤ ∫ ω, Q n ω ∂μc :=
        mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall (hQnonneg n)) (hQint n) (t ^ 2)
      have hm2 : μc.real {ω | t ^ 2 ≤ Q n ω} ≤ C / t ^ 2 := by
        rw [le_div_iff₀ ht2]
        calc μc.real {ω | t ^ 2 ≤ Q n ω} * t ^ 2
            = t ^ 2 * μc.real {ω | t ^ 2 ≤ Q n ω} := by ring
          _ ≤ ∫ ω, Q n ω ∂μc := hm1
          _ ≤ C := hCbound n
      have hconv : μc {ω | t ^ 2 ≤ Q n ω} = ENNReal.ofReal (μc.real {ω | t ^ 2 ≤ Q n ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rw [hconv]
      exact ENNReal.ofReal_le_ofReal (le_trans hm2 htC)
    refine Filter.eventually_atTop.2 ⟨max 1 ⌈t ^ 2 / r ^ 2⌉₊, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : t ^ 2 / r ^ 2 ≤ (n:ℝ) := by
      have hcl := le_trans (le_max_right 1 ⌈t ^ 2 / r ^ 2⌉₊) hn
      have : ((⌈t ^ 2 / r ^ 2⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcl
      exact le_trans (Nat.le_ceil _) this
    exact le_trans (measure_mono ((hsetsub n).trans (hsubset n hn1 hn2)))
      (le_trans (hMk n) hη₀le)
  exact tendstoInDistribution_of_tendstoInMeasure_sub Y (id : ℝ → ℝ) hclt htim
    fun n => (hYmeas n).aemeasurable

end MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    {ι : Type*} [Fintype ι]
    (u : X → ι → ℝ) (hu : ∀ p, Measurable (fun x => u x p))
    (hL2 : ∀ p, MemLp (fun x => u x p) 2 π)
    (g : (ι → ℝ) → ℝ) (hgm : Measurable g) (g' : (ι → ℝ) →L[ℝ] ℝ)
    (hg : HasFDerivAt g g' (fun p => ∫ x, u x p ∂π)) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (g (fun p => MarkovChainCLT.sampleAvg (fun x => u x p) n ω)
          - g (fun p => ∫ x, u x p ∂π)))
      atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P π)
      (gaussianReal 0
        (MarkovChainCLT.asymptoticVariance P π (fun x => g' (u x))).toNNReal) :=
  MarkovChainCLT.delta_method_aux P π hP huni u hu hL2 g hgm g' hg
