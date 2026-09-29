-- Prove2me | solution 2 for BanditAlgorithm.bandit_divergence_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-26T01:46:57.557703+00:00
-- url     : https://prove2.me/submissions/93936f39-b9b6-444b-b16f-446adfd079fe

import Theorems.Thm_BanditAlgorithm_bandit_divergence_one_step
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Lemma 15.1 and Eq. (15.1),
printed p. 198 / PDF p. 207.

The imported one-step identity is Eq. (15.2).  This file proves the formal
bridge from that identity to the full horizon decomposition by establishing
the one-step recurrence for expected arm occupation counts and then inducting
on the horizon.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
      Finset.univ).symm

private theorem measurable_pullCount_cast {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  simp_rw [pullCount_cast_eq_sum_indicator]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

private theorem integrable_pullCount {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_pullCount_cast i).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · rw [pullCount_cast_eq_sum_indicator]
        calc
          (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
              ∑ _t : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            split <;> norm_num
          _ = n := by simp

private theorem pullCount_cast_snoc {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ) =
      (armPullCount i h : ℝ) + if z.1 = i then 1 else 0 := by
  calc
    (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ) =
        ∑ t : Fin (n + 1),
          if ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) t).1 = i
          then 1 else 0 :=
      pullCount_cast_eq_sum_indicator i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)
    _ = (∑ t : Fin n, if (h t).1 = i then 1 else 0) +
          if z.1 = i then 1 else 0 := by
      rw [Fin.sum_univ_castSucc]
      simp
    _ = (armPullCount i h : ℝ) + if z.1 = i then 1 else 0 := by
      rw [pullCount_cast_eq_sum_indicator]

private theorem integrable_step_arm_indicator {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k)
    (h : BanditHistory k n) :
    Integrable (fun z : Fin k × ℝ ↦ if z.1 = i then (1 : ℝ) else 0)
      (banditStepKernel ν π n h) := by
  apply Integrable.of_mem_Icc 0 1
  · exact
      (Measurable.ite
        ((measurableSet_singleton i).preimage measurable_fst)
        measurable_const measurable_const).aemeasurable
  · exact Filter.Eventually.of_forall fun z ↦ by
      split <;> norm_num

private theorem stepKernel_integral_arm_indicator {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k)
    (h : BanditHistory k n) :
    ∫ z : Fin k × ℝ, (if z.1 = i then (1 : ℝ) else 0)
        ∂(banditStepKernel ν π n h) =
      (π.select n h).real {i} := by
  have hz := integrable_step_arm_indicator ν π i h
  rw [banditStepKernel] at hz ⊢
  rw [ProbabilityTheory.integral_compProd hz]
  calc
    (∫ x : Fin k, ∫ y : ℝ, (if x = i then (1 : ℝ) else 0)
        ∂(banditRewardKernel ν) x ∂(π.select n) h) =
        ∫ x : Fin k, (if x = i then (1 : ℝ) else 0)
          ∂(π.select n) h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hxi : x = i <;> simp [hxi]
    _ = ((π.select n) h).real {i} := by
      simpa only [Set.indicator_apply, Set.mem_singleton_iff] using
        (integral_indicator_one (μ := (π.select n) h)
          (measurableSet_singleton i))

private theorem expected_pullCount_succ {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (n + 1) =
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) +
        ∫ h, (π.select n h).real {i} ∂banditMeasure ν π n := by
  let μ := banditMeasure ν π n
  let κ := banditStepKernel ν π n
  let snoc : BanditHistory k n × (Fin k × ℝ) →
      BanditHistory k (n + 1) :=
    fun p ↦ Fin.snoc p.1 p.2
  have hsnoc : Measurable snoc := measurable_banditHistorySnoc
  have hrewrite :
      (fun p ↦ (armPullCount i (snoc p) : ℝ)) =
        fun p ↦ (armPullCount i p.1 : ℝ) +
          if p.2.1 = i then 1 else 0 := by
    funext p
    exact pullCount_cast_snoc i p.1 p.2
  have hold : Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        (armPullCount i p.1 : ℝ)) (μ.compProd κ) := by
    have hi : Integrable
        (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
        (Measure.map Prod.fst (μ.compProd κ)) := by
      change Integrable
        (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
        ((μ.compProd κ).fst)
      rw [Measure.fst_compProd]
      exact integrable_pullCount ν π i
    exact hi.comp_aemeasurable measurable_fst.aemeasurable
  have hnew : Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        if p.2.1 = i then (1 : ℝ) else 0) (μ.compProd κ) := by
    apply Integrable.of_mem_Icc 0 1
    · exact
        (Measurable.ite
          ((measurableSet_singleton i).preimage
            (measurable_fst.comp measurable_snd))
          measurable_const measurable_const).aemeasurable
    · exact Filter.Eventually.of_forall fun p ↦ by
        split <;> norm_num
  rw [banditMeasure,
    integral_map hsnoc.aemeasurable
      (measurable_pullCount_cast i).aestronglyMeasurable]
  change (∫ p, (armPullCount i (snoc p) : ℝ) ∂(μ.compProd κ)) = _
  rw [hrewrite, integral_add hold hnew]
  rw [Measure.integral_compProd hold, Measure.integral_compProd hnew]
  congr 1
  · simp [μ, κ]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun h ↦
      stepKernel_integral_arm_indicator ν π i h

private theorem expected_pullCount_nonneg {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    0 ≤ ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n :=
  integral_nonneg fun h ↦ by positivity

private theorem expected_selection_nonneg {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    0 ≤ ∫ h, (π.select n h).real {i} ∂banditMeasure ν π n :=
  integral_nonneg fun h ↦ by positivity

end BanditAlgorithm

theorem solution {k : ℕ}
    (ν ν' : BanditAlgorithm.StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditAlgorithm.BanditPolicy k) (n : ℕ) :
    klDiv (BanditAlgorithm.banditMeasure ν π n)
        (BanditAlgorithm.banditMeasure ν' π n) =
      ∑ i, ENNReal.ofReal
          (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
            ∂BanditAlgorithm.banditMeasure ν π n) *
        klDiv (ν.P i) (ν'.P i) := by
  classical
  induction n with
  | zero =>
      simp [BanditAlgorithm.banditMeasure, BanditAlgorithm.armPullCount]
  | succ n ih =>
      rw [BanditAlgorithm.bandit_divergence_one_step ν ν' hKL π, ih]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [BanditAlgorithm.expected_pullCount_succ]
      rw [ENNReal.ofReal_add
        (BanditAlgorithm.expected_pullCount_nonneg ν π i)
        (BanditAlgorithm.expected_selection_nonneg ν π i)]
      rw [add_mul]
