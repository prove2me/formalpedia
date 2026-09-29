-- Prove2me | solution 1 for BanditAlgorithm.best_arm_identification_sample_complexity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:14:39.991843+00:00
-- url     : https://prove2.me/submissions/09bbd95f-6662-4d9c-9ea1-f443549d2560

import Theorems.Thm_BanditAlgorithm_best_arm_identification_stopping_change_of_measure
import Theorems.Thm_BanditAlgorithm_baiComplexity_mul_le_total_of_information_constraints_of_pos

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution {k : ℕ}
    (𝓔 : Set (StochasticBandit k)) (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (π : BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Fin k)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hsound : IsSoundBAI δ π τ ψ 𝓔) (ν : StochasticBandit k) (hν : ν ∈ 𝓔) :
    baiComplexity ν 𝓔 * ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
      ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π := by
  classical
  let μ := banditTrajMeasure ν π
  let Eτ : ℝ≥0∞ := ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ
  change baiComplexity ν 𝓔 *
      ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤ Eτ
  by_cases hEtop : Eτ = ⊤
  · simp [hEtop]
  have hk : 0 < k := by
    by_contra hk'
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk'
    subst k
    let h0 : BanditHistory 0 0 := fun t ↦ t.elim0
    letI : IsProbabilityMeasure (π.select 0 h0) :=
      IsMarkovKernel.isProbabilityMeasure h0
    have hu : π.select 0 h0 Set.univ = 1 := measure_univ
    have hempty : (Set.univ : Set (Fin 0)) = ∅ := by
      ext i
      exact i.elim0
    rw [hempty, measure_empty] at hu
    exact zero_ne_one hu
  let c : Fin k → ℝ≥0∞ := fun i ↦
    ∫⁻ ω, ∑' t : ℕ,
      if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0 ∂μ
  have hinfo : ∀ ν' ∈ baiAlternatives 𝓔 ν,
      ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
        ∑ i, c i * InformationTheory.klDiv (ν.P i) (ν'.P i) := by
    intro ν' hν'
    exact best_arm_identification_stopping_change_of_measure
      𝓔 δ hδ π τ ψ hτ hψ hsound ν ν' hν hν'
        (lt_top_iff_ne_top.mpr (by simpa [Eτ, μ] using hEtop))
  have hopt :=
    baiComplexity_mul_le_total_of_information_constraints_of_pos
      hk 𝓔 ν c (ENNReal.ofReal (Real.log (1 / (4 * δ)))) hinfo
  refine hopt.trans_eq ?_
  have hmeas_term (i : Fin k) (t : ℕ) :
      Measurable (fun ω : ℕ → Fin k × ℝ ↦
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0) := by
    apply Measurable.ite
    · have haction : Measurable
          (fun ω : ℕ → Fin k × ℝ ↦ (ω t).1) :=
        measurable_fst.comp (measurable_pi_apply t)
      have hstop : MeasurableSet
          {ω : ℕ → Fin k × ℝ | (t : ℕ∞) < τ ω} :=
        ((banditFiltration k).le t) _ (hτ.measurableSet_gt t)
      exact hstop.inter
        (haction (measurableSet_singleton i))
    · exact measurable_const
    · exact measurable_const
  have hmeas_count (i : Fin k) :
      Measurable (fun ω : ℕ → Fin k × ℝ ↦
        ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0) :=
    Measurable.ennreal_tsum fun t ↦ hmeas_term i t
  rw [show (∑ i, c i) =
      ∫⁻ ω, ∑ i, ∑' t : ℕ,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0 ∂μ by
        symm
        exact lintegral_finset_sum Finset.univ
          (fun i _hi ↦ hmeas_count i)]
  congr 1
  funext ω
  calc
    (∑ i, ∑' t : ℕ,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0) =
        ∑' i : Fin k, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0 := by
            rw [tsum_fintype]
    _ = ∑' t : ℕ, ∑' i : Fin k,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0 :=
      ENNReal.tsum_comm
    _ = ∑' t : ℕ, ∑ i : Fin k,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0 := by
            congr 1
            funext t
            rw [tsum_fintype]
    _ = ∑' t : ℕ, if (t : ℕ∞) < τ ω then (1 : ℝ≥0∞) else 0 := by
      apply tsum_congr
      intro t
      by_cases ht : (t : ℕ∞) < τ ω
      · simp [ht]
      · simp [ht]
    _ = (τ ω : ℝ≥0∞) := by
      cases hτω : τ ω with
      | top => simp [ENNReal.tsum_one]
      | coe n =>
          simp only [ENat.coe_lt_coe, ENat.toENNReal_coe]
          rw [tsum_eq_sum (s := Finset.range n)]
          · calc
              ∑ t ∈ Finset.range n,
                  (if t < n then (1 : ℝ≥0∞) else 0) =
                  ∑ _t ∈ Finset.range n, (1 : ℝ≥0∞) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    simp [Finset.mem_range.mp ht]
              _ = (n : ℝ≥0∞) := by simp
          · intro b hb
            simp only [Finset.mem_range, not_lt] at hb
            simp [hb]
