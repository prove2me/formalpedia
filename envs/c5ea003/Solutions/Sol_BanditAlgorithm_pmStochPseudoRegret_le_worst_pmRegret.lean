-- Prove2me | solution 1 for BanditAlgorithm.pmStochPseudoRegret_le_worst_pmRegret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T19:13:03.639306+00:00
-- url     : https://prove2.me/submissions/38eb8854-9e44-400a-8374-eb5b3ff0e65e

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators


namespace BanditAlgorithm

private lemma pmSignalMeasure_apply_sum
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (u : Fin d → ℝ)
    (c : Fin k) (s : Set 𝕊) (hs : MeasurableSet s) :
    pmSignalMeasure G u c s =
      ∑ j, ENNReal.ofReal (u j) * s.indicator 1 (G.Φ c j) := by
  rw [pmSignalMeasure, Measure.map_apply (measurable_of_countable _) hs,
    pmOutcomeMeasure, Measure.sum_apply _
      ((measurable_of_countable (G.Φ c)) hs)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_preimage, Pi.one_apply, tsum_fintype]
  rfl

private lemma pmStochStepKernel_eq_outcome_mixture
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (h : PMHistory k 𝕊 n) :
    pmStochStepKernel G π u hu n h =
      Measure.sum fun j : Fin d =>
        ENNReal.ofReal (u j) • pmStepKernel G π j n h := by
  classical
  ext s hs
  rw [pmStochStepKernel, Kernel.compProd_apply hs,
    Measure.sum_apply _ hs]
  simp_rw [Kernel.comap_apply]
  change (∫⁻ b, pmSignalMeasure G u b (Prod.mk b ⁻¹' s) ∂π.select n h) = _
  simp only [tsum_fintype, Measure.smul_apply, smul_eq_mul]
  rw [show (∫⁻ a, pmSignalMeasure G u a (Prod.mk a ⁻¹' s) ∂π.select n h) =
      ∫⁻ a, ∑ j, ENNReal.ofReal (u j) *
        s.indicator 1 (a, G.Φ a j) ∂π.select n h by
    apply lintegral_congr
    intro a
    simpa only [Set.mem_preimage] using
      pmSignalMeasure_apply_sum G u a _ (measurable_prodMk_left hs)]
  rw [lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [lintegral_const_mul _ (measurable_of_countable _)]
    rw [pmStepKernel, Kernel.map_apply' _ (measurable_of_countable _) _ hs]
    rw [← lintegral_indicator_one
      ((measurable_of_countable (fun a : Fin k => (a, G.Φ a j))) hs)]
    congr 1
  · intro j hj
    exact measurable_of_countable _

private lemma pmMeasure_compProd_stochStep_eq_outcome_mixture
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (μ : Measure (PMHistory k 𝕊 n)) [SFinite μ] :
    μ.compProd (pmStochStepKernel G π u hu n) =
      Measure.sum fun j : Fin d =>
        ENNReal.ofReal (u j) • μ.compProd (pmStepKernel G π j n) := by
  classical
  ext s hs
  rw [Measure.compProd_apply hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, tsum_fintype]
  rw [show (∫⁻ h, pmStochStepKernel G π u hu n h (Prod.mk h ⁻¹' s) ∂μ) =
      ∫⁻ h, ∑ j, ENNReal.ofReal (u j) *
        pmStepKernel G π j n h (Prod.mk h ⁻¹' s) ∂μ by
    apply lintegral_congr
    intro h
    rw [pmStochStepKernel_eq_outcome_mixture G π u hu h,
      Measure.sum_apply _ (measurable_prodMk_left hs)]
    simp only [Measure.smul_apply, smul_eq_mul, tsum_fintype]]
  rw [lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [lintegral_const_mul _ (Kernel.measurable_kernel_prodMk_left hs),
      Measure.compProd_apply hs]
  · intro j hj
    exact (Kernel.measurable_kernel_prodMk_left hs).const_mul _

private noncomputable def pmOutcomeSeqWeight {d n : ℕ}
    (u : Fin d → ℝ) (i : Fin n → Fin d) : ℝ≥0∞ :=
  ∏ t, ENNReal.ofReal (u (i t))

private lemma pmOutcomeSeqWeight_sum
    {d n : ℕ} (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    ∑ i : Fin n → Fin d, pmOutcomeSeqWeight u i = 1 := by
  classical
  simp only [pmOutcomeSeqWeight]
  have hmass : ∑ j : Fin d, ENNReal.ofReal (u j) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hu.1 i), hu.2]
    simp
  calc
    ∑ x : Fin n → Fin d, ∏ t, ENNReal.ofReal (u (x t)) =
        ∏ _t : Fin n, ∑ j : Fin d, ENNReal.ofReal (u j) := by
      simpa using (Finset.sum_prod_piFinset (ι := Fin n) Finset.univ
        (fun _ : Fin n => fun j : Fin d => ENNReal.ofReal (u j)))
    _ = 1 := by simp [hmass]

private theorem pmStochMeasure_eq_outcome_mixture
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    ∀ n : ℕ,
      pmStochMeasure G π u hu n =
        Measure.sum fun i : Fin n → Fin d =>
          pmOutcomeSeqWeight u i • pmMeasure G π n i := by
  classical
  intro n
  induction n with
  | zero =>
      rw [pmStochMeasure]
      ext s hs
      rw [Measure.sum_apply _ hs]
      simp [pmOutcomeSeqWeight, pmMeasure]
  | succ n ih =>
      rw [pmStochMeasure, ih, Measure.compProd_sum_left]
      simp_rw [Measure.compProd_smul_left]
      simp_rw [pmMeasure_compProd_stochStep_eq_outcome_mixture G π u hu]
      ext s hs
      have hpre : MeasurableSet ((fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
          Fin.snoc p.1 p.2) ⁻¹' s) := measurable_pmHistorySnoc hs
      have hsum (i : Fin n → Fin d) :
          (Measure.sum fun j : Fin d => ENNReal.ofReal (u j) •
              (pmMeasure G π n i).compProd (pmStepKernel G π j n))
              ((fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) => Fin.snoc p.1 p.2) ⁻¹' s) =
            ∑' j : Fin d, (ENNReal.ofReal (u j) •
              (pmMeasure G π n i).compProd (pmStepKernel G π j n))
              ((fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) => Fin.snoc p.1 p.2) ⁻¹' s) :=
        Measure.sum_apply _ hpre
      simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
      simp_rw [Measure.map_apply measurable_pmHistorySnoc hs]
      rw [Measure.sum_apply _ hpre]
      simp only [Measure.smul_apply, smul_eq_mul]
      simp_rw [hsum, Measure.smul_apply, smul_eq_mul]
      simp_rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_prod]
      let e : ((Fin n → Fin d) × Fin d) ≃ (Fin (n + 1) → Fin d) :=
        { toFun := fun p => Fin.snoc p.1 p.2
          invFun := fun f => (Fin.init f, f (Fin.last n))
          left_inv := by
            intro p
            apply Prod.ext
            · exact Fin.init_snoc
                (α := fun _ : Fin (n + 1) => Fin d) (p := p.1) (x := p.2)
            · exact Fin.snoc_last
                (α := fun _ : Fin (n + 1) => Fin d) (p := p.1) (x := p.2)
          right_inv := Fin.snoc_init_self }
      rw [← e.tsum_eq]
      congr 1
      funext f
      change pmOutcomeSeqWeight u f.1 *
          (ENNReal.ofReal (u f.2) *
            ((pmMeasure G π n f.1).compProd (pmStepKernel G π f.2 n))
              ((fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) => Fin.snoc p.1 p.2) ⁻¹' s)) =
        pmOutcomeSeqWeight u (Fin.snoc f.1 f.2) *
          pmMeasure G π (n + 1) (Fin.snoc f.1 f.2) s
      have hweight : pmOutcomeSeqWeight u (Fin.snoc f.1 f.2) =
          pmOutcomeSeqWeight u f.1 * ENNReal.ofReal (u f.2) := by
        rw [pmOutcomeSeqWeight, Fin.prod_univ_castSucc]
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rfl
      rw [hweight]
      rw [pmMeasure]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [Measure.map_apply measurable_pmHistorySnoc hs]
      ring

private lemma integrable_of_finite_domain
    {α : Type*} [Finite α] [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun x : α => ‖f x‖)
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

private def pmActualGapSum
    {k d n : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (i : Fin n → Fin d)
    (a : Fin k) (h : PMHistory k 𝕊 n) : ℝ :=
  ∑ t, (G.L (h t).1 (i t) - G.L a (i t))

private def pmExpectedGapSum
    {k d n : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (u : Fin d → ℝ)
    (a : Fin k) (h : PMHistory k 𝕊 n) : ℝ :=
  ∑ t, (pmExpectedLoss G u (h t).1 - pmExpectedLoss G u a)

private lemma measurable_pmActualGapSum
    {k d n : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (i : Fin n → Fin d) (a : Fin k) :
    Measurable (pmActualGapSum G i a : PMHistory k 𝕊 n → ℝ) := by
  unfold pmActualGapSum
  apply Finset.measurable_sum
  intro t ht
  exact ((measurable_of_countable
    (fun c : Fin k => G.L c (i t))).comp
      (measurable_fst.comp (measurable_pi_apply t))).sub measurable_const

private lemma measurable_pmExpectedGapSum
    {k d n : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (u : Fin d → ℝ) (a : Fin k) :
    Measurable (pmExpectedGapSum G u a : PMHistory k 𝕊 n → ℝ) := by
  unfold pmExpectedGapSum
  apply Finset.measurable_sum
  intro t ht
  exact ((measurable_of_countable
    (fun c : Fin k => pmExpectedLoss G u c)).comp
      (measurable_fst.comp (measurable_pi_apply t))).sub measurable_const

private lemma integral_pmStepKernel_gap
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (j : Fin d) (a : Fin k) (h : PMHistory k 𝕊 n) :
    (∫ z, (G.L z.1 j - G.L a j) ∂pmStepKernel G π j n h) =
      ∫ c, (G.L c j - G.L a j) ∂π.select n h := by
  let φ : Fin k → Fin k × 𝕊 := fun c => (c, G.Φ c j)
  let f : Fin k × 𝕊 → ℝ := fun z => G.L z.1 j - G.L a j
  have hφ : Measurable φ := measurable_of_countable _
  have hf : Measurable f :=
    (((measurable_of_countable (fun c : Fin k => G.L c j)).comp
      measurable_fst).sub measurable_const)
  rw [pmStepKernel, Kernel.map_apply (π.select n) hφ h]
  change (∫ z, f z ∂Measure.map φ (π.select n h)) = _
  rw [MeasureTheory.integral_map hφ.aemeasurable hf.aestronglyMeasurable]

private lemma integral_pmStochStepKernel_expectedGap
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (a : Fin k) (h : PMHistory k 𝕊 n) :
    (∫ z, (pmExpectedLoss G u z.1 - pmExpectedLoss G u a)
        ∂pmStochStepKernel G π u hu n h) =
      ∫ c, (pmExpectedLoss G u c - pmExpectedLoss G u a)
        ∂π.select n h := by
  let f : Fin k × 𝕊 → ℝ := fun z =>
    pmExpectedLoss G u z.1 - pmExpectedLoss G u a
  have hfmeas : Measurable f :=
    ((measurable_of_countable
      (fun c : Fin k => pmExpectedLoss G u c)).comp measurable_fst).sub
        measurable_const
  have hfint : Integrable f (pmStochStepKernel G π u hu n h) :=
    integrable_of_finite_domain hfmeas
  rw [pmStochStepKernel, ProbabilityTheory.integral_compProd hfint]
  simp only [Kernel.comap_apply]
  haveI (c : Fin k) : IsProbabilityMeasure (pmSignalMeasure G u c) :=
    pmSignalMeasure_isProbabilityMeasure G u hu c
  apply integral_congr_ae
  filter_upwards [] with c
  change (∫ _y : 𝕊, (pmExpectedLoss G u c - pmExpectedLoss G u a)
      ∂pmSignalMeasure G u c) = _
  simp

private lemma pmStep_gap_outcome_average
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (a : Fin k) (h : PMHistory k 𝕊 n) :
    ∑ j : Fin d, (pmOutcomeSeqWeight u (fun _ : Fin 1 => j)).toReal *
        (∫ z, (G.L z.1 j - G.L a j) ∂pmStepKernel G π j n h) =
      ∫ z, (pmExpectedLoss G u z.1 - pmExpectedLoss G u a)
        ∂pmStochStepKernel G π u hu n h := by
  simp only [pmOutcomeSeqWeight, Fin.prod_univ_succ, Fin.prod_univ_zero,
    mul_one, ENNReal.toReal_ofReal (hu.1 _)]
  simp_rw [integral_pmStepKernel_gap G π]
  rw [integral_pmStochStepKernel_expectedGap G π u hu a h]
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards [] with c
    unfold pmExpectedLoss
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro j hj
    exact integrable_of_finite_domain (measurable_of_countable _)

private lemma integral_pmActualGapSum_snoc
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (i : Fin n → Fin d) (j : Fin d) (a : Fin k) :
    (∫ h, pmActualGapSum G (Fin.snoc i j) a h
        ∂pmMeasure G π (n + 1) (Fin.snoc i j)) =
      (∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i) +
        ∫ h, ∫ z, (G.L z.1 j - G.L a j)
          ∂pmStepKernel G π j n h ∂pmMeasure G π n i := by
  let snocFn : PMHistory k 𝕊 n × (Fin k × 𝕊) → PMHistory k 𝕊 (n + 1) :=
    fun p => Fin.snoc p.1 p.2
  let F : PMHistory k 𝕊 (n + 1) → ℝ :=
    pmActualGapSum G (Fin.snoc i j) a
  have hF : Measurable F := measurable_pmActualGapSum G (Fin.snoc i j) a
  have hsnoc : Measurable snocFn := measurable_pmHistorySnoc
  rw [pmMeasure]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change (∫ h, F h ∂Measure.map snocFn
      ((pmMeasure G π n i).compProd (pmStepKernel G π j n))) = _
  rw [MeasureTheory.integral_map hsnoc.aemeasurable hF.aestronglyMeasurable]
  have hsplit : ∀ p : PMHistory k 𝕊 n × (Fin k × 𝕊),
      F (snocFn p) = pmActualGapSum G i a p.1 +
        (G.L p.2.1 j - G.L a j) := by
    intro p
    unfold F snocFn pmActualGapSum
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [hsplit]
  have hprefixMeas : Measurable
      (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) => pmActualGapSum G i a p.1) :=
    (measurable_pmActualGapSum G i a).comp measurable_fst
  have hlastMeas : Measurable
      (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) => G.L p.2.1 j - G.L a j) :=
    ((measurable_of_countable (fun c : Fin k => G.L c j)).comp
      (measurable_fst.comp measurable_snd)).sub measurable_const
  have hprefixInt := integrable_of_finite_domain (μ :=
    (pmMeasure G π n i).compProd (pmStepKernel G π j n)) hprefixMeas
  have hlastInt := integrable_of_finite_domain (μ :=
    (pmMeasure G π n i).compProd (pmStepKernel G π j n)) hlastMeas
  rw [integral_add hprefixInt hlastInt]
  rw [Measure.integral_compProd hprefixInt,
    Measure.integral_compProd hlastInt]
  haveI (h : PMHistory k 𝕊 n) :
      IsProbabilityMeasure (pmStepKernel G π j n h) := inferInstance
  simp

private lemma pmStochPseudoRegret_succ
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) (a : Fin k) :
    pmStochPseudoRegret G π u hu (n + 1) a =
      pmStochPseudoRegret G π u hu n a +
        ∫ h, ∫ z, (pmExpectedLoss G u z.1 - pmExpectedLoss G u a)
          ∂pmStochStepKernel G π u hu n h ∂pmStochMeasure G π u hu n := by
  let snocFn : PMHistory k 𝕊 n × (Fin k × 𝕊) → PMHistory k 𝕊 (n + 1) :=
    fun p => Fin.snoc p.1 p.2
  let F : PMHistory k 𝕊 (n + 1) → ℝ := pmExpectedGapSum G u a
  have hF : Measurable F := measurable_pmExpectedGapSum G u a
  have hsnoc : Measurable snocFn := measurable_pmHistorySnoc
  rw [pmStochPseudoRegret]
  change (∫ h, F h ∂pmStochMeasure G π u hu (n + 1)) = _
  rw [pmStochMeasure]
  rw [MeasureTheory.integral_map hsnoc.aemeasurable hF.aestronglyMeasurable]
  have hsplit : ∀ p : PMHistory k 𝕊 n × (Fin k × 𝕊),
      F (snocFn p) = pmExpectedGapSum G u a p.1 +
        (pmExpectedLoss G u p.2.1 - pmExpectedLoss G u a) := by
    intro p
    unfold F snocFn pmExpectedGapSum
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [hsplit]
  have hprefixMeas : Measurable
      (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) => pmExpectedGapSum G u a p.1) :=
    (measurable_pmExpectedGapSum G u a).comp measurable_fst
  have hlastMeas : Measurable
      (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
        pmExpectedLoss G u p.2.1 - pmExpectedLoss G u a) :=
    ((measurable_of_countable (fun c : Fin k => pmExpectedLoss G u c)).comp
      (measurable_fst.comp measurable_snd)).sub measurable_const
  have hprefixInt := integrable_of_finite_domain (μ :=
    (pmStochMeasure G π u hu n).compProd (pmStochStepKernel G π u hu n))
      hprefixMeas
  have hlastInt := integrable_of_finite_domain (μ :=
    (pmStochMeasure G π u hu n).compProd (pmStochStepKernel G π u hu n))
      hlastMeas
  rw [integral_add hprefixInt hlastInt]
  rw [Measure.integral_compProd hprefixInt, Measure.integral_compProd hlastInt]
  haveI (h : PMHistory k 𝕊 n) :
      IsProbabilityMeasure (pmStochStepKernel G π u hu n h) := inferInstance
  simp only [Prod.fst, Prod.snd]
  simp [pmStochPseudoRegret, pmExpectedGapSum]

private lemma integral_pmStochMeasure_eq_outcome_mixture
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (f : PMHistory k 𝕊 n → ℝ)
    (hfint : Integrable f (pmStochMeasure G π u hu n)) :
    (∫ h, f h ∂pmStochMeasure G π u hu n) =
      ∑ i : Fin n → Fin d, (pmOutcomeSeqWeight u i).toReal *
        ∫ h, f h ∂pmMeasure G π n i := by
  rw [pmStochMeasure_eq_outcome_mixture G π u hu n] at hfint ⊢
  rw [MeasureTheory.integral_sum_measure hfint]
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MeasureTheory.integral_smul_measure]
  simp only [smul_eq_mul]

private theorem pmStochPseudoRegret_eq_outcome_mixture
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (a : Fin k) : ∀ n : ℕ,
    pmStochPseudoRegret G π u hu n a =
      ∑ i : Fin n → Fin d, (pmOutcomeSeqWeight u i).toReal *
        ∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i := by
  classical
  intro n
  induction n with
  | zero =>
      simp [pmStochPseudoRegret, pmExpectedGapSum, pmActualGapSum,
        pmOutcomeSeqWeight]
  | succ n ih =>
      rw [pmStochPseudoRegret_succ G π u hu a, ih]
      let e : ((Fin n → Fin d) × Fin d) ≃ (Fin (n + 1) → Fin d) :=
        { toFun := fun p => Fin.snoc p.1 p.2
          invFun := fun f => (Fin.init f, f (Fin.last n))
          left_inv := by
            intro p
            apply Prod.ext
            · exact Fin.init_snoc
                (α := fun _ : Fin (n + 1) => Fin d) (p := p.1) (x := p.2)
            · exact Fin.snoc_last
                (α := fun _ : Fin (n + 1) => Fin d) (p := p.1) (x := p.2)
          right_inv := Fin.snoc_init_self }
      rw [← e.sum_comp]
      simp only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type]
      simp_rw [integral_pmActualGapSum_snoc G π]
      have hweight (i : Fin n → Fin d) (j : Fin d) :
          (pmOutcomeSeqWeight u (Fin.snoc i j)).toReal =
            (pmOutcomeSeqWeight u i).toReal * u j := by
        simp only [pmOutcomeSeqWeight, Fin.prod_univ_castSucc]
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hu.1 j)]
      simp_rw [hweight]
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · calc
          ∑ i : Fin n → Fin d,
              (pmOutcomeSeqWeight u i).toReal *
                (∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i) =
              ∑ i : Fin n → Fin d,
                (pmOutcomeSeqWeight u i).toReal *
                  (∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i) *
                  ∑ j : Fin d, u j := by rw [hu.2]; simp
          _ = ∑ i : Fin n → Fin d, ∑ j : Fin d,
              (pmOutcomeSeqWeight u i).toReal * u j *
                ∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
      · let fcur : PMHistory k 𝕊 n → ℝ := fun h =>
            ∫ z, (pmExpectedLoss G u z.1 - pmExpectedLoss G u a)
              ∂pmStochStepKernel G π u hu n h
        have hfcurMeas : Measurable fcur := by
          exact (((measurable_of_countable
            (fun c : Fin k => pmExpectedLoss G u c)).comp
              measurable_fst).sub measurable_const).stronglyMeasurable.integral_kernel.measurable
        have hfcurInt : Integrable fcur (pmStochMeasure G π u hu n) :=
          integrable_of_finite_domain hfcurMeas
        rw [integral_pmStochMeasure_eq_outcome_mixture G π u hu fcur hfcurInt]
        apply Finset.sum_congr rfl
        intro i hi
        have hpoint (h : PMHistory k 𝕊 n) :
            fcur h = ∑ j : Fin d, u j *
              ∫ z, (G.L z.1 j - G.L a j) ∂pmStepKernel G π j n h := by
          symm
          simpa only [fcur, pmOutcomeSeqWeight, Fin.prod_univ_succ,
            Fin.prod_univ_zero, mul_one, ENNReal.toReal_ofReal (hu.1 _)] using
              pmStep_gap_outcome_average G π u hu a h
        calc
          (pmOutcomeSeqWeight u i).toReal *
              ∫ h, fcur h ∂pmMeasure G π n i =
              (pmOutcomeSeqWeight u i).toReal *
                ∫ h, ∑ j : Fin d, u j *
                  ∫ z, (G.L z.1 j - G.L a j)
                    ∂pmStepKernel G π j n h ∂pmMeasure G π n i := by
                congr 1
                apply integral_congr_ae
                filter_upwards [] with h
                exact hpoint h
          _ = (pmOutcomeSeqWeight u i).toReal *
                ∑ j : Fin d, ∫ h, u j *
                  (∫ z, (G.L z.1 j - G.L a j)
                    ∂pmStepKernel G π j n h) ∂pmMeasure G π n i := by
                rw [integral_finset_sum]
                intro j hj
                have hfjMeas : Measurable (fun h : PMHistory k 𝕊 n =>
                    ∫ z, (G.L z.1 j - G.L a j)
                      ∂pmStepKernel G π j n h) := by
                  exact (((measurable_of_countable
                    (fun c : Fin k => G.L c j)).comp measurable_fst).sub
                      measurable_const).stronglyMeasurable.integral_kernel.measurable
                exact (integrable_of_finite_domain hfjMeas).const_mul _
          _ = ∑ j : Fin d, (pmOutcomeSeqWeight u i).toReal * u j *
                ∫ h, ∫ z, (G.L z.1 j - G.L a j)
                  ∂pmStepKernel G π j n h ∂pmMeasure G π n i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                rw [MeasureTheory.integral_const_mul]
                ring

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (n : ℕ) (a : Fin k) :
    pmStochPseudoRegret G π u hu n a ≤
      ⨆ i : Fin n → Fin d, pmRegret G π n i := by
  classical
  rw [pmStochPseudoRegret_eq_outcome_mixture G π u hu a n]
  have hcomp (i : Fin n → Fin d) :
      (∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i) ≤
        pmRegret G π n i := by
    unfold pmRegret pmActualGapSum
    exact le_ciSup (Finite.bddAbove_range (fun b : Fin k =>
      ∫ h, ∑ t, (G.L (h t).1 (i t) - G.L b (i t)) ∂pmMeasure G π n i)) a
  have hseq (i : Fin n → Fin d) :
      pmRegret G π n i ≤ ⨆ i : Fin n → Fin d, pmRegret G π n i :=
    le_ciSup (Finite.bddAbove_range _) i
  have hweightSum :
      ∑ i : Fin n → Fin d, (pmOutcomeSeqWeight u i).toReal = 1 := by
    rw [← ENNReal.toReal_sum (by
      intro i hi
      exact ENNReal.prod_ne_top fun t ht => ENNReal.ofReal_ne_top)]
    rw [pmOutcomeSeqWeight_sum u hu]
    simp
  calc
    ∑ i : Fin n → Fin d, (pmOutcomeSeqWeight u i).toReal *
          ∫ h, pmActualGapSum G i a h ∂pmMeasure G π n i ≤
        ∑ i : Fin n → Fin d, (pmOutcomeSeqWeight u i).toReal *
          pmRegret G π n i := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hcomp i) ENNReal.toReal_nonneg
    _ ≤ ∑ i : Fin n → Fin d, (pmOutcomeSeqWeight u i).toReal *
          (⨆ i : Fin n → Fin d, pmRegret G π n i) := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hseq i) ENNReal.toReal_nonneg
    _ = ⨆ i : Fin n → Fin d, pmRegret G π n i := by
          rw [← Finset.sum_mul, hweightSum, one_mul]

end BanditAlgorithm
