-- Prove2me | solution 1 for MarkovChainCLT.uniformIntegrable_sq_partialSum_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T10:55:47.619788+00:00
-- url     : https://prove2.me/submissions/699ae1a5-50b7-4f85-93ec-3b506186214a

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MeasureTheory_uniformIntegrable_one_of_sq_bounded_approx
import Theorems.Thm_MarkovChainCLT_integral_pow_four_partialSum_le_of_bounded_of_exp_alpha
import Theorems.Thm_MarkovChainCLT_exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment
import Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const
import Theorems.Thm_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

private noncomputable def truncLow (T x : ℝ) : ℝ := if T < |x| then 0 else x

private noncomputable def truncHigh (T x : ℝ) : ℝ := if T < |x| then x else 0

private theorem truncLow_add_truncHigh (T x : ℝ) : truncLow T x + truncHigh T x = x := by
  unfold truncLow truncHigh
  split_ifs <;> ring

private theorem measurable_truncLow (T : ℝ) : Measurable (truncLow T) := by
  unfold truncLow
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_const
    measurable_id

private theorem measurable_truncHigh (T : ℝ) : Measurable (truncHigh T) := by
  unfold truncHigh
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) measurable_id
    measurable_const

private theorem abs_truncLow_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |truncLow T x| ≤ T := by
  unfold truncLow
  split_ifs with h
  · simpa using hT
  · exact le_of_not_gt h

private theorem memLp_two_of_stationary (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (hL2 : MemLp (Y 0) 2 P)
    (i : ℕ) : MemLp (Y i) 2 P := by
  have hmi : Measurable (fun ω => (fun n => Y (n + i) ω)) :=
    measurable_pi_lambda _ fun n => hY (n + i)
  have hm0 : Measurable (fun ω => (fun n => Y n ω)) :=
    measurable_pi_lambda _ fun n => hY n
  have he : Measurable (fun x : ℕ → ℝ => x 0) := measurable_pi_apply 0
  have h1 := congrArg (fun μ => Measure.map (fun x : ℕ → ℝ => x 0) μ) (hstat i)
  simp only [Measure.map_map he hmi, Measure.map_map he hm0] at h1
  have e1 : ((fun x : ℕ → ℝ => x 0) ∘ fun ω => (fun n => Y (n + i) ω)) = Y i := by
    funext ω; simp
  have e2 : ((fun x : ℕ → ℝ => x 0) ∘ fun ω => (fun n => Y n ω)) = Y 0 := by
    funext ω; simp
  rw [e1, e2] at h1
  have h0 : MemLp (id : ℝ → ℝ) 2 (Measure.map (Y 0) P) := by
    rw [memLp_map_measure_iff (by fun_prop) (hY 0).aemeasurable]
    simpa using hL2
  rw [← h1] at h0
  simpa using h0.comp_of_map (hY i).aemeasurable


end Helpers

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by
  -- the log moment puts `Y 0` in `L²`
  have hL2 : MemLp (Y 0) 2 P :=
    (MarkovChainCLT.memLp_two_and_logMoment_sub_const P (Y 0) (hY 0) hmom 0).1
  -- summable covariances give the linear growth of the variance
  have hvarlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P)
      atTop (𝓝 (seqAsymptoticVariance P Y)) :=
    MarkovChainCLT.tendsto_inv_mul_integral_sq_partialSum P Y hY hstat hL2 hsum
  -- recoding preserves stationarity and does not increase the mixing coefficients
  have hstat_comp : ∀ g : ℝ → ℝ, Measurable g →
      IsStrictlyStationary P (fun i ω => g (Y i ω)) :=
    fun g hg => MarkovChainCLT.isStrictlyStationary_comp_of_measurable P Y hY hstat g hg
  have halpha_comp : ∀ g : ℝ → ℝ, Measurable g → ∀ n,
      alphaMixingCoef P (fun i ω => g (Y i ω)) n ≤ alphaMixingCoef P Y n :=
    fun g hg n => (MarkovChainCLT.alphaMixingCoef_comp_nonneg_le_of_finite P Y g hg n).2
  -- the fourth-moment inequality for the truncated part
  have hfourth : ∀ X : ℕ → Ω → ℝ, (∀ n, Measurable (X n)) → IsStrictlyStationary P X →
      (∫ ω, X 0 ω ∂P = 0) → ∀ M : ℝ, (∀ i, ∀ ω, |X i ω| ≤ M) →
      (∀ n, alphaMixingCoef P X n ≤ c * a ^ n) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
        ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 4 ∂P ≤ K * (n : ℝ) ^ 2 :=
    fun X hXm hXs hXc M hM hXa =>
      MarkovChainCLT.integral_pow_four_partialSum_le_of_bounded_of_exp_alpha P X hXm hXs hXc M hM
        c a ha0 ha1 hXa
  -- the smallness of the truncated tail
  have htail : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n, (truncHigh T (Y i ω)
        - ∫ ω', truncHigh T (Y 0 ω') ∂P)) ^ 2 ∂P ≤ ε * n :=
    fun ε hε =>
      MarkovChainCLT.exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment P Y hY hstat
        hcent c a ha0 ha1 hα hmom ε hε
  classical
  set σ2 : ℝ := seqAsymptoticVariance P Y with hσ2def
  set v : ℕ → ℝ := fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P with hvdef
  have hSmeas : ∀ n : ℕ, Measurable (fun ω => ∑ i ∈ Finset.range n, Y i ω) :=
    fun n => Finset.measurable_sum _ fun i _ => hY i
  have hYL2 : ∀ i, MemLp (Y i) 2 P := memLp_two_of_stationary P Y hY hstat hL2
  have hSL2 : ∀ n : ℕ, MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P :=
    fun n => memLp_finsetSum _ (fun i _ => hYL2 i)
  have hSsq : ∀ n : ℕ, Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) P :=
    fun n => (hSL2 n).integrable_sq
  have hv0 : ∀ n, 0 ≤ v n := fun n => integral_nonneg fun ω => sq_nonneg _
  -- the variance of the partial sums grows linearly
  obtain ⟨N₀, hN₀1, hN₀v⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → σ2 * n / 2 ≤ v n := by
    have hev : ∀ᶠ n : ℕ in atTop, σ2 / 2 < (n : ℝ)⁻¹ * v n :=
      hvarlim.eventually (eventually_gt_nhds (by linarith))
    obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
    refine ⟨max N 1, le_max_right _ _, fun n hn => ?_⟩
    have h1 := (hN n (le_trans (le_max_left _ _) hn)).1
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have := mul_le_mul_of_nonneg_left h1.le hnpos.le
    rw [← mul_assoc] at this
    field_simp at this ⊢
    nlinarith [this]
  refine uniformIntegrable_one_of_sq_bounded_approx P _
    (fun n => ((hSmeas n).pow_const 2).div_const _)
    (fun n ω => div_nonneg (sq_nonneg _) (hv0 n)) (fun n => (hSsq n).div_const _)
    (fun n => by rw [integral_div]; exact div_self_le_one _) ?_
  intro ε hε
  -- choose the truncation level
  obtain ⟨T, hT0, hTb⟩ := htail (ε * σ2 / 4) (by positivity)
  set m : ℝ := ∫ ω, truncLow T (Y 0 ω) ∂P with hmdef
  set mt : ℝ := ∫ ω, truncHigh T (Y 0 ω) ∂P with hmtdef
  set X : ℕ → Ω → ℝ := fun i ω => truncLow T (Y i ω) - m with hXdef
  set Z : ℕ → Ω → ℝ := fun i ω => truncHigh T (Y i ω) - mt with hZdef
  have hlowmeas : ∀ i, Measurable (fun ω => truncLow T (Y i ω)) :=
    fun i => (measurable_truncLow T).comp (hY i)
  have hhighmeas : ∀ i, Measurable (fun ω => truncHigh T (Y i ω)) :=
    fun i => (measurable_truncHigh T).comp (hY i)
  have hlowint : ∀ i, Integrable (fun ω => truncLow T (Y i ω)) P := by
    intro i
    refine Integrable.mono' (integrable_const T) (hlowmeas i).aestronglyMeasurable ?_
    exact Eventually.of_forall fun ω => by
      simpa using abs_truncLow_le hT0.le (Y i ω)
  have hYint : ∀ i, Integrable (Y i) P := fun i => (hYL2 i).integrable (by norm_num)
  have hhighint : ∀ i, Integrable (fun ω => truncHigh T (Y i ω)) P := by
    intro i
    have : (fun ω => truncHigh T (Y i ω)) = fun ω => Y i ω - truncLow T (Y i ω) := by
      funext ω
      have := truncLow_add_truncHigh T (Y i ω)
      linarith
    rw [this]
    exact (hYint i).sub (hlowint i)
  have hmmt : m + mt = 0 := by
    rw [hmdef, hmtdef, ← integral_add (hlowint 0) (hhighint 0)]
    rw [← hcent]
    exact integral_congr_ae (Eventually.of_forall fun ω => truncLow_add_truncHigh T (Y 0 ω))
  have hXmeas : ∀ i, Measurable (X i) := fun i => (hlowmeas i).sub measurable_const
  have hZmeas : ∀ i, Measurable (Z i) := fun i => (hhighmeas i).sub measurable_const
  have hXcent : ∫ ω, X 0 ω ∂P = 0 := by
    rw [hXdef]
    simp only
    rw [integral_sub (hlowint 0) (integrable_const m)]
    simp [← hmdef]
  have hXbdd : ∀ i, ∀ ω, |X i ω| ≤ T + |m| := by
    intro i ω
    calc |X i ω| ≤ |truncLow T (Y i ω)| + |m| := by
          simpa [hXdef] using abs_sub (truncLow T (Y i ω)) m
      _ ≤ T + |m| := by linarith [abs_truncLow_le hT0.le (Y i ω)]
  have hXstat : IsStrictlyStationary P X :=
    hstat_comp (fun x => truncLow T x - m) ((measurable_truncLow T).sub measurable_const)
  have hXalpha : ∀ n, alphaMixingCoef P X n ≤ c * a ^ n := fun n =>
    le_trans (halpha_comp (fun x => truncLow T x - m)
      ((measurable_truncLow T).sub measurable_const) n) (hα n)
  obtain ⟨K, hK0, hKb⟩ := hfourth X hXmeas hXstat hXcent (T + |m|) hXbdd hXalpha
  -- the two halves of the partial sum
  set A : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, X i ω with hAdef
  set B : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, Z i ω with hBdef
  have hsplit : ∀ n ω, (∑ i ∈ Finset.range n, Y i ω) = A n ω + B n ω := by
    intro n ω
    rw [hAdef, hBdef]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := truncLow_add_truncHigh T (Y i ω)
    simp only [hXdef, hZdef]
    linarith
  have hAmeas : ∀ n, Measurable (A n) := fun n => Finset.measurable_sum _ fun i _ => hXmeas i
  have hBmeas : ∀ n, Measurable (B n) := fun n => Finset.measurable_sum _ fun i _ => hZmeas i
  have hAbdd : ∀ n, ∀ ω, |A n ω| ≤ n * (T + |m|) := by
    intro n ω
    calc |A n ω| ≤ ∑ i ∈ Finset.range n, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range n, (T + |m|) :=
          Finset.sum_le_sum fun i _ => hXbdd i ω
      _ = n * (T + |m|) := by simp [Finset.sum_const, nsmul_eq_mul, mul_add]
  have hZL2 : ∀ i, MemLp (Z i) 2 P := by
    intro i
    have h1 : MemLp (fun ω => truncHigh T (Y i ω)) 2 P := by
      have heq : (fun ω => truncHigh T (Y i ω)) = fun ω => Y i ω - truncLow T (Y i ω) := by
        funext ω
        have := truncLow_add_truncHigh T (Y i ω)
        linarith
      rw [heq]
      refine (hYL2 i).sub ?_
      refine MemLp.of_bound (hlowmeas i).aestronglyMeasurable T ?_
      exact Eventually.of_forall fun ω => by
        simpa using abs_truncLow_le hT0.le (Y i ω)
    exact h1.sub (memLp_const mt)
  have hBL2 : ∀ n, MemLp (B n) 2 P := fun n => memLp_finsetSum _ (fun i _ => hZL2 i)
  refine ⟨N₀, fun n ω => 2 * (A n ω) ^ 2 / v n, fun n ω => 2 * (B n ω) ^ 2 / v n,
    16 * K / σ2 ^ 2, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the truncated part is bounded, hence in `L²`
    intro n _
    refine MemLp.of_bound ((((hAmeas n).pow_const 2).const_mul 2).div_const
      (v n)).aestronglyMeasurable (2 * ((n : ℝ) * (T + |m|)) ^ 2 / v n) ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hv0 n)]
    gcongr
    rw [abs_of_nonneg (by positivity)]
    have h1 : |A n ω| ≤ (n : ℝ) * (T + |m|) := hAbdd n ω
    have h2 : (A n ω) ^ 2 ≤ ((n : ℝ) * (T + |m|)) ^ 2 := by
      nlinarith [sq_abs (A n ω), abs_nonneg (A n ω)]
    linarith
  · -- the tail part is integrable
    intro n _
    exact (((hBL2 n).integrable_sq).const_mul 2).div_const _
  · exact fun n _ ω => by positivity
  · exact fun n _ ω => by positivity
  · -- the pointwise domination `(A + B)² ≤ 2A² + 2B²`
    intro n _ ω
    show (∑ i ∈ Finset.range n, Y i ω) ^ 2 / v n
      ≤ 2 * (A n ω) ^ 2 / v n + 2 * (B n ω) ^ 2 / v n
    rw [hsplit n ω]
    rcases eq_or_lt_of_le (hv0 n) with h | h
    · simp [← h]
    · have hr : 2 * (A n ω) ^ 2 / v n + 2 * (B n ω) ^ 2 / v n
          = (2 * (A n ω) ^ 2 + 2 * (B n ω) ^ 2) / v n := by ring
      rw [hr, div_le_div_iff_of_pos_right h]
      nlinarith [sq_nonneg (A n ω - B n ω)]
  · -- the `L²` bound for the truncated part
    intro n hn
    have hvpos : 0 < v n := by
      have hn1 : 1 ≤ n := le_trans hN₀1 hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have := hN₀v n hn
      nlinarith
    have hvlow : σ2 * n / 2 ≤ v n := hN₀v n hn
    have heq : ∀ ω, (2 * (A n ω) ^ 2 / v n) ^ 2 = 4 / v n ^ 2 * (A n ω) ^ 4 := by
      intro ω; field_simp; ring
    rw [integral_congr_ae (Eventually.of_forall heq), integral_const_mul]
    have h4 : ∫ ω, (A n ω) ^ 4 ∂P ≤ K * (n : ℝ) ^ 2 := hKb n
    have hnpos : (0 : ℝ) < n := by
      have hn1 : 1 ≤ n := le_trans hN₀1 hn
      exact_mod_cast hn1
    have hsq : (σ2 * n / 2) ^ 2 ≤ v n ^ 2 := by
      have h0 : 0 ≤ σ2 * n / 2 := by positivity
      nlinarith
    have hint0 : 0 ≤ ∫ ω, (A n ω) ^ 4 ∂P := by
      refine integral_nonneg fun ω => by positivity
    calc 4 / v n ^ 2 * ∫ ω, (A n ω) ^ 4 ∂P
        ≤ 4 / (σ2 * n / 2) ^ 2 * (K * (n : ℝ) ^ 2) := by
          gcongr
      _ = 16 * K / σ2 ^ 2 := by field_simp; ring
  · -- the `L¹` bound for the tail part
    intro n hn
    have hvlow : σ2 * n / 2 ≤ v n := hN₀v n hn
    have hnpos : (0 : ℝ) < n := by
      have hn1 : 1 ≤ n := le_trans hN₀1 hn
      exact_mod_cast hn1
    have hvpos : 0 < v n := by nlinarith
    have hB : ∫ ω, (B n ω) ^ 2 ∂P ≤ ε * σ2 / 4 * n := hTb n
    have hB0 : 0 ≤ ∫ ω, (B n ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have heq : ∫ ω, 2 * (B n ω) ^ 2 / v n ∂P = 2 / v n * ∫ ω, (B n ω) ^ 2 ∂P := by
      have : ∀ ω, 2 * (B n ω) ^ 2 / v n = 2 / v n * (B n ω) ^ 2 := by
        intro ω; field_simp
      rw [integral_congr_ae (Eventually.of_forall this), integral_const_mul]
    rw [heq]
    calc 2 / v n * ∫ ω, (B n ω) ^ 2 ∂P ≤ 2 / (σ2 * n / 2) * (ε * σ2 / 4 * n) := by
          gcongr
      _ = ε := by field_simp; ring
