-- Prove2me | solution 1 for BanditAlgorithm.bandit_adaptive_stopped_centered_sum_tail_half
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T04:38:52.201015+00:00
-- url     : https://prove2.me/submissions/0259d29b-c996-48cb-8810-caa12f4c4ce5

import Definitions.Def_ucbStoppedCenteredSum
import Definitions.Def_banditHistoryPrefix
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
Canonical-model stopped-reward concentration for an arbitrary (possibly
randomized) bandit policy.  This is the reward-stack / bounded optional
stopping bridge from Lattimore--Szepesvári §4.6, Exercise 4.4, used in the
proofs of Theorems 7.1 and 8.1.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem armPullCount_snoc_ast {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add]
  simp only [armPullCount]
  have hset (g : BanditHistory k n) :
      ({t | (g t).1 = i}.toFinset.card : ℝ) =
        ∑ t, if (g t).1 = i then 1 else 0 := by
    have hs : {t | (g t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (g t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (g t).1 = i)
        Finset.univ).symm
  rw [hset]
  have hsnoc :
      (({t |
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset.card :
          ℕ) : ℝ) =
        ∑ t, if
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i
        then 1 else 0 := by
    have hs : {t |
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset =
        Finset.univ.filter
          (fun t ↦
            (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin (n + 1) ↦
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i)
        Finset.univ).symm
  rw [hsnoc, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem measurable_armPullCount_cast_ast {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    measurable_const measurable_const

private theorem measurable_stoppedScoreFactor_ast {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)) := by
  apply Measurable.exp
  have hcount : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        (armPullCount i p.1 : ℝ)) :=
    (measurable_armPullCount_cast_ast i).comp measurable_fst
  have hlt : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        armPullCount i p.1 < u} := by
    simpa only [Nat.cast_lt] using measurableSet_lt hcount
      (measurable_const : Measurable
        (fun _ : BanditHistory k m × (Fin k × ℝ) ↦ (u : ℝ)))
  have heq : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} :=
    (measurableSet_singleton i).preimage measurable_snd.fst
  exact Measurable.ite (hlt.inter heq)
    ((measurable_snd.snd.sub measurable_const).const_mul t
      |>.sub measurable_const)
    measurable_const

private theorem integrable_banditStepKernel_stoppedScoreFactor_ast
    {k m : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) (π : BanditPolicy k)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    Integrable (fun z : Fin k × ℝ ↦ Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0))
      (banditStepKernel ν π m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_stoppedScoreFactor_ast ν i u t).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    by_cases hc : armPullCount i h < u ∧ a = i
    · have hlt := hc.1
      have hai := hc.2
      subst a
      simp only [Function.comp_apply, id_eq, hlt, and_self, if_pos]
      rw [show (banditRewardKernel ν) i = ν.P i by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      change Integrable
        (fun y : ℝ ↦ Real.exp
          (t * (y - banditArmMean ν i) - t ^ 2 / 8)) (ν.P i)
      have hbase :=
        (hν.2 i).integrable_exp_mul t |>.mul_const
          (Real.exp (-(t ^ 2 / 8)))
      convert hbase using 1
      funext y
      rw [← Real.exp_add]
      congr 1
    · simp [hc]
  · exact Integrable.of_finite

private theorem banditStepKernel_integral_stoppedScoreFactor_le_one_ast
    {k m : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) (π : BanditPolicy k)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    ∫ z : Fin k × ℝ, Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
      ∂banditStepKernel ν π m h ≤ 1 := by
  have hint :=
    integrable_banditStepKernel_stoppedScoreFactor_ast
      ν hν π h i u t
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, Real.exp
        (if armPullCount i h < u ∧ a = i then
          t * (y - banditArmMean ν i) - t ^ 2 / 8 else 0)
        ∂((banditRewardKernel ν).comap Prod.snd measurable_snd) (h, a)
        ∂(π.select m) h) ≤
        ∫ _a, (1 : ℝ) ∂(π.select m) h := by
      apply integral_mono_ae hint.integral_compProd (integrable_const 1)
      filter_upwards with a
      rw [Kernel.comap_apply]
      by_cases hc : armPullCount i h < u ∧ a = i
      · have hlt := hc.1
        have hai := hc.2
        subst a
        simp only [hlt, and_self, if_pos]
        rw [show (banditRewardKernel ν) i = ν.P i by
          simp [banditRewardKernel, Kernel.ofFunOfCountable]]
        have hm := (hν.2 i).mgf_le t
        rw [mgf] at hm
        have hm' :
            (∫ y, Real.exp (t * (y - banditArmMean ν i)) ∂ν.P i) ≤
              Real.exp (t ^ 2 / 8) := by
          convert hm using 1 <;> norm_num <;> ring_nf
        calc
          (∫ y, Real.exp
              (t * (y - banditArmMean ν i) - t ^ 2 / 8) ∂ν.P i) =
              Real.exp (-(t ^ 2 / 8)) *
                ∫ y, Real.exp (t * (y - banditArmMean ν i)) ∂ν.P i := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with y
            rw [← Real.exp_add]
            congr 1
            ring
          _ ≤ Real.exp (-(t ^ 2 / 8)) * Real.exp (t ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left hm' (Real.exp_nonneg _)
          _ = 1 := by
            rw [← Real.exp_add]
            ring_nf
            simp
      · simp [hc]
    _ = 1 := by simp

private theorem armStoppedCenteredSum_snoc_ast {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

private theorem min_armPullCount_snoc_ast {k m : ℕ}
    (i : Fin k) (u : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    min (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)) u =
      min (armPullCount i h) u +
        if armPullCount i h < u ∧ z.1 = i then 1 else 0 := by
  rw [armPullCount_snoc_ast]
  by_cases hi : z.1 = i
  · by_cases hlt : armPullCount i h < u
    · simp [hi, hlt]
      omega
    · simp [hi, hlt]
      omega
  · simp [hi]

private theorem measurable_armStoppedCenteredSum_ast {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable (fun h : BanditHistory k (m + 1) ↦
          (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_cast_ast i).comp hinit
      have hlt : MeasurableSet {h : BanditHistory k (m + 1) |
          armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet {h : BanditHistory k (m + 1) |
          (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

private noncomputable def armStoppedExpScoreAst {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ)
    (h : BanditHistory k m) : ℝ :=
  Real.exp (t * armStoppedCenteredSum ν i u m h -
    t ^ 2 / 8 * ((min (armPullCount i h) u : ℕ) : ℝ))

private theorem measurable_armStoppedExpScoreAst {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ) := by
  apply Measurable.exp
  apply
    (measurable_const.mul (measurable_armStoppedCenteredSum_ast ν i u m)).sub
  have hmin : Measurable (fun h : BanditHistory k m ↦
      min (armPullCount i h : ℝ) (u : ℝ)) :=
    (measurable_armPullCount_cast_ast i).min measurable_const
  simpa only [Nat.cast_min] using measurable_const.mul hmin

private theorem armStoppedExpScoreAst_snoc {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedExpScoreAst ν i u t
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedExpScoreAst ν i u t h *
        Real.exp (if armPullCount i h < u ∧ z.1 = i then
          t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0) := by
  rw [armStoppedExpScoreAst, armStoppedExpScoreAst,
    armStoppedCenteredSum_snoc_ast, min_armPullCount_snoc_ast, Nat.cast_add]
  by_cases hlt : armPullCount i h < u
  · by_cases hi : z.1 = i
    · simp only [hlt, hi, and_self, if_pos, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [hlt, hi]
  · simp [hlt]

private theorem integrable_compProd_armStoppedExpScoreAst_factor
    {k : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    {m : ℕ} (μ : Measure (BanditHistory k m)) [IsProbabilityMeasure μ]
    (i : Fin k) (u : ℕ) (t : ℝ)
    (hold : Integrable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      armStoppedExpScoreAst ν i u t p.1 * Real.exp
        (if armPullCount i p.1 < u ∧ p.2.1 = i then
          t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    armStoppedExpScoreAst ν i u t p.1 * Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_armStoppedExpScoreAst ν i u t).comp measurable_fst).mul
      (measurable_stoppedScoreFactor_ast ν i u t)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_banditStepKernel_stoppedScoreFactor_ast
        ν hν π h i u t).const_mul
          (armStoppedExpScoreAst ν i u t h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ armStoppedExpScoreAst ν i u t h :=
      Real.exp_nonneg _
    have hcond :=
      banditStepKernel_integral_stoppedScoreFactor_le_one_ast
        ν hν π h i u t
    have hinner_nonneg :
        0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖armStoppedExpScoreAst ν i u t h * Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)‖
      ∂banditStepKernel ν π m h) ≤ ‖armStoppedExpScoreAst ν i u t h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

private theorem armStoppedExpScoreAst_integrable_and_integral_le_one
    {k : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) (t : ℝ) : ∀ m : ℕ,
    Integrable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ)
      (banditMeasure ν π m) ∧
    ∫ h, armStoppedExpScoreAst ν i u t h ∂banditMeasure ν π m ≤ 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;>
        simp [banditMeasure, armStoppedExpScoreAst,
          armStoppedCenteredSum, armPullCount]
  | succ m ih =>
      let μ := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc :
          BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        armStoppedExpScoreAst ν i u t p.1 * Real.exp
          (if armPullCount i p.1 < u ∧ p.2.1 = i then
            t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
      have hrewrite :
          (fun p ↦ armStoppedExpScoreAst ν i u t (snoc p)) = F := by
        funext p
        exact armStoppedExpScoreAst_snoc ν i u t p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) :=
        integrable_compProd_armStoppedExpScoreAst_factor
          ν hν μ i u t ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_armStoppedExpScoreAst
            (m := m + 1) ν i u t).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable
          (fun p ↦ armStoppedExpScoreAst ν i u t (snoc p))
          (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_armStoppedExpScoreAst
              (m := m + 1) ν i u t).aestronglyMeasurable]
        change (∫ p, armStoppedExpScoreAst ν i u t (snoc p)
          ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, armStoppedExpScoreAst ν i u t h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, armStoppedExpScoreAst ν i u t h * Real.exp
              (if armPullCount i h < u ∧ z.1 = i then
                t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
              ∂κ h) ≤ armStoppedExpScoreAst ν i u t h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_stoppedScoreFactor_le_one_ast
                ν hν π h i u t)
          _ ≤ 1 := ih.2

theorem adaptive_armStoppedCenteredSum_upper_tail_half
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
      Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedExpScoreAst_integrable_and_integral_le_one
      ν hν (π := π) i u (4 * t) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) =
      armStoppedExpScoreAst ν i u (4 * t) := by
    funext h
    rw [armStoppedExpScoreAst]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have h4t : 0 ≤ 4 * t := mul_nonneg (by norm_num) ht
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) h4t hint
  calc
    μ.real {h : BanditHistory k n |
        (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh _)
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) *
          mgf X μ (4 * t) := hchern
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-2 * (u : ℝ) * t ^ 2) := by
      congr 1
      ring

theorem adaptive_armStoppedCenteredSum_lower_tail_half
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
      Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    -armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedExpScoreAst_integrable_and_integral_le_one
      ν hν (π := π) i u (-(4 * t)) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) =
      armStoppedExpScoreAst ν i u (-(4 * t)) := by
    funext h
    rw [armStoppedExpScoreAst]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have h4t : 0 ≤ 4 * t := mul_nonneg (by norm_num) ht
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) h4t hint
  calc
    μ.real {h : BanditHistory k n |
        armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      change armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t at hh
      have hh' : (u : ℝ) * t ≤
          -armStoppedCenteredSum ν i u n h := by
        linarith
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh' _)
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) *
          mgf X μ (4 * t) := hchern
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-2 * (u : ℝ) * t ^ 2) := by
      congr 1
      ring

private noncomputable def armCenteredSumAst {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

private theorem armCenteredSumAst_snoc {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armCenteredSumAst ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSumAst ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSumAst, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

theorem armStoppedCenteredSum_eq_pullCount_mul_empirical_sub_mean
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  have hstop :
      armStoppedCenteredSum ν i u m h = armCenteredSumAst ν i h := by
    induction m with
    | zero => simp [armStoppedCenteredSum, armCenteredSumAst]
    | succ m ih =>
        rw [← Fin.snoc_init_self h] at hcount ⊢
        rw [armPullCount_snoc_ast] at hcount
        rw [armStoppedCenteredSum_snoc_ast, armCenteredSumAst_snoc]
        by_cases hi : (h (Fin.last m)).1 = i
        · have hprev : armPullCount i (Fin.init h) < u := by
            simp [hi] at hcount
            omega
          rw [if_pos ⟨hprev, hi⟩, if_pos hi,
            ih (Fin.init h) (Nat.le_of_lt hprev)]
        · have hprev : armPullCount i (Fin.init h) ≤ u := by
            simpa [hi] using hcount
          rw [if_neg (fun hc ↦ hi hc.2), if_neg hi,
            ih (Fin.init h) hprev]
  rw [hstop]
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSumAst, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

private theorem measurable_banditHistoryPrefixAt_ast {k n : ℕ}
    (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem prefixAt_snoc_castSucc_ast {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) r.castSucc =
      banditHistoryPrefixAt h r := by
  funext s
  unfold banditHistoryPrefixAt
  have hsr : s.val < r.val := by simpa using s.isLt
  have hsn : s.val < n := lt_trans hsr r.isLt
  rw [Fin.snoc]
  rw [dif_pos hsn]
  simp

private theorem prefixAt_snoc_last_ast {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem banditMeasure_map_init_ast {k m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) :
    (banditMeasure ν π (m + 1)).map
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) =
      banditMeasure ν π m := by
  rw [banditMeasure]
  rw [MeasureTheory.Measure.map_map
    (by fun_prop :
      Measurable (fun h : BanditHistory k (m + 1) ↦ Fin.init h))
    measurable_banditHistorySnoc]
  have hfun :
      ((fun h : BanditHistory k (m + 1) ↦ Fin.init h) ∘
        (fun h : BanditHistory k m × (Fin k × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) h.1 h.2)) =
        Prod.fst := by
    funext p
    simp
  rw [hfun]
  change Measure.fst
      ((banditMeasure ν π m).compProd (banditStepKernel ν π m)) =
    banditMeasure ν π m
  exact MeasureTheory.Measure.fst_compProd
    (banditMeasure ν π m) (banditStepKernel ν π m)

theorem banditMeasure_map_historyPrefixAt
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) :
    (banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) =
      banditMeasure ν π r.val := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h (Fin.last n)) =
            banditMeasure ν π n
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h (Fin.last n)) =
          (fun h ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa using
              prefixAt_snoc_last_ast (Fin.init h) (h (Fin.last n))]
        exact banditMeasure_map_init_ast ν π
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h s.castSucc) =
            banditMeasure ν π s.val
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h s.castSucc) =
          (fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
            (fun h : BanditHistory k (n + 1) ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa [Function.comp_apply] using
              prefixAt_snoc_castSucc_ast
                (Fin.init h) (h (Fin.last n)) s]
        calc
          (banditMeasure ν π (n + 1)).map
              ((fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)) =
              ((banditMeasure ν π (n + 1)).map
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)).map
                (fun g : BanditHistory k n ↦
                  banditHistoryPrefixAt g s) := by
            symm
            exact MeasureTheory.Measure.map_map
              (measurable_banditHistoryPrefixAt_ast s)
              (by fun_prop :
                Measurable
                  (fun h : BanditHistory k (n + 1) ↦ Fin.init h))
          _ = banditMeasure ν π s.val := by
            rw [banditMeasure_map_init_ast ν π, ih s]

end BanditAlgorithm

theorem solution
    {k n : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hν : BanditAlgorithm.IsSubgaussianBandit (1 / 2) ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          (u : ℝ) * t ≤
            BanditAlgorithm.armStoppedCenteredSum ν i u n h} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) ∧
      (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          BanditAlgorithm.armStoppedCenteredSum ν i u n h ≤
            -(u : ℝ) * t} ≤
        Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  exact ⟨
    BanditAlgorithm.adaptive_armStoppedCenteredSum_upper_tail_half
      ν hν i u ht,
    BanditAlgorithm.adaptive_armStoppedCenteredSum_lower_tail_half
      ν hν i u ht⟩
