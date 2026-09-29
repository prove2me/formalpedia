-- Prove2me | solution 1 for BanditAlgorithm.mdp_empirical_row_deviation_at_sample_size_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-03T03:42:36.108999+00:00
-- url     : https://prove2.me/submissions/92366176-e32b-475e-8464-af8378fe36a4

import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ
import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_BanditAlgorithm_l1_deviation_union_bound
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped NNReal ENNReal

namespace Emp

variable {S A : ℕ}

/-- The indicator that round `t` is one of the first `m` visits to `(s₀, a₀)`. -/
noncomputable def actv (s0 : Fin S) (a0 : Fin A) (m : ℕ) {N : ℕ}
    (h : MDPTrajectory S A N) (t : ℕ) : ℝ :=
  if ht : t < N then
    (if h ⟨t, ht⟩ = (s0, a0) ∧ mdpVisitCount h t s0 a0 < m then (1 : ℝ) else 0)
  else 0

/-- The centred indicator of the subset `Asub` of successor states. -/
noncomputable def chiq (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A)
    (Asub : Finset (Fin S)) (s' : Fin S) : ℝ :=
  (if s' ∈ Asub then (1 : ℝ) else 0) - ∑ s'' ∈ Asub, (M.P s0 a0 s'' : ℝ)

/-- The capped sum of centred successor indicators over the first `m` visits. -/
noncomputable def Wsum (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A)
    (Asub : Finset (Fin S)) (m : ℕ) {N : ℕ} (h : MDPTrajectory S A N) : ℝ :=
  ∑ t ∈ Finset.range N, (if ht : t + 1 < N then
      actv s0 a0 m h t * chiq M s0 a0 Asub ((h ⟨t + 1, ht⟩).1) else 0)

/-- The number of terms actually contributing to `Wsum`. -/
noncomputable def Cntr (s0 : Fin S) (a0 : Fin A) (m : ℕ) {N : ℕ}
    (h : MDPTrajectory S A N) : ℝ :=
  ∑ t ∈ Finset.range N, (if t + 1 < N then actv s0 a0 m h t else 0)

lemma snoc_castSucc' {N : ℕ} (g : MDPTrajectory S A N) (p : Fin S × Fin A)
    (t : ℕ) (ht : t < N) :
    (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) ⟨t, by omega⟩ = g ⟨t, ht⟩ := by
  have : (⟨t, by omega⟩ : Fin (N + 1)) = (Fin.castSucc ⟨t, ht⟩) := rfl
  rw [this, Fin.snoc_castSucc]

lemma visitCount_snoc {N : ℕ} (g : MDPTrajectory S A N) (p : Fin S × Fin A)
    (s0 : Fin S) (a0 : Fin A) (t : ℕ) (ht : t ≤ N) :
    mdpVisitCount (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) t s0 a0
      = mdpVisitCount g t s0 a0 := by
  classical
  simp only [mdpVisitCount]
  rw [← Finset.card_map ⟨Fin.castSucc, Fin.castSucc_injective N⟩]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hi, hval⟩
    have hiN : i.val < N := by omega
    refine ⟨⟨i.val, hiN⟩, ⟨hi, ?_⟩, ?_⟩
    · rw [← hval]
      exact (snoc_castSucc' g p i.val hiN).symm
    · exact Fin.ext rfl
  · rintro ⟨j, ⟨hj, hjval⟩, rfl⟩
    refine ⟨hj, ?_⟩
    rw [show (Fin.castSucc j : Fin (N+1)) = ⟨j.val, by omega⟩ from rfl,
      snoc_castSucc' g p j.val j.isLt]
    exact hjval

lemma actv_snoc {N : ℕ} (g : MDPTrajectory S A N) (p : Fin S × Fin A)
    (s0 : Fin S) (a0 : Fin A) (m : ℕ) (t : ℕ) (ht : t < N) :
    actv s0 a0 m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) t = actv s0 a0 m g t := by
  simp only [actv, dif_pos ht, dif_pos (show t < N + 1 by omega)]
  rw [snoc_castSucc' g p t ht, visitCount_snoc g p s0 a0 t (le_of_lt ht)]

end Emp

namespace Emp
variable {S A : ℕ}

lemma Wsum_snoc (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m N : ℕ) (g : MDPTrajectory S A (N + 1)) (p : Fin S × Fin A) :
    Wsum M s0 a0 Asub m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p)
      = Wsum M s0 a0 Asub m g + actv s0 a0 m g N * chiq M s0 a0 Asub p.1 := by
  classical
  simp only [Wsum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ (n := N)]
  rw [Finset.sum_range_succ (f := fun t ↦ if ht : t + 1 < N + 1 then
      actv s0 a0 m g t * chiq M s0 a0 Asub ((g ⟨t + 1, ht⟩).1) else 0)]
  have hlast : (dite (N + 1 + 1 < N + 2)
      (fun ht ↦ actv s0 a0 m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) (N + 1)
        * chiq M s0 a0 Asub (((Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) ⟨N + 1 + 1, ht⟩).1))
      (fun _ ↦ (0 : ℝ))) = 0 := dif_neg (by omega)
  have hlast2 : (dite (N + 1 < N + 1)
      (fun ht ↦ actv s0 a0 m g N * chiq M s0 a0 Asub ((g ⟨N + 1, ht⟩).1))
      (fun _ ↦ (0 : ℝ))) = 0 := dif_neg (by omega)
  rw [hlast, hlast2, add_zero, add_zero]
  have hmid : (dite (N + 1 < N + 2)
      (fun ht ↦ actv s0 a0 m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) N
        * chiq M s0 a0 Asub (((Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) ⟨N + 1, ht⟩).1))
      (fun _ ↦ (0 : ℝ))) = actv s0 a0 m g N * chiq M s0 a0 Asub p.1 := by
    rw [dif_pos (by omega)]
    rw [actv_snoc g p s0 a0 m N (by omega)]
    congr 2
    show ((Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) (Fin.last (N + 1))).1 = p.1
    rw [Fin.snoc_last]
  rw [hmid]
  congr 1
  refine Finset.sum_congr rfl fun t htmem ↦ ?_
  have ht : t < N := Finset.mem_range.1 htmem
  rw [dif_pos (show t + 1 < N + 2 by omega), dif_pos (show t + 1 < N + 1 by omega),
    actv_snoc g p s0 a0 m t (by omega)]
  congr 2
  exact congrArg Prod.fst (snoc_castSucc' g p (t + 1) (by omega))

lemma Cntr_snoc (s0 : Fin S) (a0 : Fin A) (m N : ℕ) (g : MDPTrajectory S A (N + 1))
    (p : Fin S × Fin A) :
    Cntr s0 a0 m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p)
      = Cntr s0 a0 m g + actv s0 a0 m g N := by
  classical
  simp only [Cntr]
  rw [Finset.sum_range_succ, Finset.sum_range_succ (n := N),
    Finset.sum_range_succ (f := fun t ↦ if t + 1 < N + 1 then actv s0 a0 m g t else 0)]
  rw [if_neg (show ¬ (N + 1 + 1 < N + 2) by omega), if_neg (show ¬ (N + 1 < N + 1) by omega),
    add_zero, add_zero, if_pos (show N + 1 < N + 2 by omega),
    actv_snoc g p s0 a0 m N (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun t htmem ↦ ?_
  have ht : t < N := Finset.mem_range.1 htmem
  rw [if_pos (show t + 1 < N + 2 by omega), if_pos (show t + 1 < N + 1 by omega),
    actv_snoc g p s0 a0 m t (by omega)]

lemma Wsum_one (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m : ℕ) (h : MDPTrajectory S A 1) : Wsum M s0 a0 Asub m h = 0 := by
  simp [Wsum]

lemma Cntr_one (s0 : Fin S) (a0 : Fin A) (m : ℕ) (h : MDPTrajectory S A 1) :
    Cntr s0 a0 m h = 0 := by
  simp [Cntr]

lemma Wsum_zero (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m : ℕ) (h : MDPTrajectory S A 0) : Wsum M s0 a0 Asub m h = 0 := by
  simp [Wsum]

lemma Cntr_zero (s0 : Fin S) (a0 : Fin A) (m : ℕ) (h : MDPTrajectory S A 0) :
    Cntr s0 a0 m h = 0 := by
  simp [Cntr]

end Emp

namespace Emp
variable {S A : ℕ}

lemma integral_stateDist (d : MDPStateDistribution S) (f : Fin S → ℝ) :
    ∫ s, f s ∂d.toMeasure = ∑ s, (d.prob s : ℝ) * f s := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have : d.toMeasure {s} = (d.prob s : ℝ≥0∞) := by
    simp only [MDPStateDistribution.toMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton s), Set.indicator_apply,
      Set.mem_singleton_iff]
    rw [Finset.sum_eq_single s] <;> simp +contextual
  rw [measureReal_def, this, smul_eq_mul]
  simp

lemma row_sum_one (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A) :
    ∑ s', (M.P s0 a0 s' : ℝ) = 1 := by
  have := M.P_sum_one s0 a0
  have : ((∑ s', M.P s0 a0 s' : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [this]
  simpa using this

/-- **Hoeffding's lemma at one transition.**  The centred indicator of a subset of
successor states has moment generating function at most `exp (λ² / 8)` under the
true transition row. -/
lemma mgf_chiq_le (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A)
    (Asub : Finset (Fin S)) (lam : ℝ) :
    ∑ s', (M.P s0 a0 s' : ℝ) * Real.exp (lam * chiq M s0 a0 Asub s')
      ≤ Real.exp (lam ^ 2 / 8) := by
  classical
  set q : ℝ := ∑ s'' ∈ Asub, (M.P s0 a0 s'' : ℝ) with hq
  set d := M.transitionDist s0 a0 with hd
  haveI : IsProbabilityMeasure d.toMeasure := d.instIsProbabilityMeasure
  have hdprob : ∀ s', (d.prob s' : ℝ) = (M.P s0 a0 s' : ℝ) := fun s' ↦ rfl
  have hIcc : ∀ᵐ s' ∂d.toMeasure, chiq M s0 a0 Asub s' ∈ Set.Icc (-q) (1 - q) := by
    refine Filter.Eventually.of_forall fun s' ↦ ?_
    simp only [chiq, ← hq]
    constructor
    · have : (0 : ℝ) ≤ if s' ∈ Asub then (1 : ℝ) else 0 := by split <;> norm_num
      linarith
    · have : (if s' ∈ Asub then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
      linarith
  have hmean : ∫ s', chiq M s0 a0 Asub s' ∂d.toMeasure = 0 := by
    rw [integral_stateDist]
    simp only [chiq, ← hq, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h1 : ∑ s', (d.prob s' : ℝ) * (if s' ∈ Asub then (1 : ℝ) else 0) = q := by
      rw [hq]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_mem]
      simp only [Finset.univ_inter]
      exact Finset.sum_congr rfl fun s' _ ↦ hdprob s'
    have h2 : ∑ s', (d.prob s' : ℝ) = 1 := by
      simp only [hdprob]
      exact row_sum_one M s0 a0
    rw [h1, h2, one_mul, sub_self]
  have hsg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := d.toMeasure) (X := chiq M s0 a0 Asub)
    (measurable_of_countable _).aemeasurable hIcc hmean
  have hmgf := hsg.mgf_le lam
  have hnn : (((‖(1 - q) - (-q)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    have : (1 : ℝ) - q - (-q) = 1 := by ring
    rw [this]
    simp
    norm_num
  rw [hnn] at hmgf
  have hmgfeq : mgf (chiq M s0 a0 Asub) d.toMeasure lam
      = ∑ s', (M.P s0 a0 s' : ℝ) * Real.exp (lam * chiq M s0 a0 Asub s') := by
    rw [mgf, integral_stateDist]
    exact Finset.sum_congr rfl fun s' _ ↦ by rw [hdprob]
  rw [hmgfeq] at hmgf
  refine le_trans hmgf (le_of_eq ?_)
  congr 1
  ring

end Emp

namespace Emp
variable {S A : ℕ}

lemma integral_step_fst (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (m : ℕ) (g : MDPTrajectory S A (m + 1)) (f : Fin S → ℝ) :
    ∫ p, f p.1 ∂(mdpStepKernel M μ0 π (m + 1) g)
      = ∑ s', (M.P (g (Fin.last m)).1 (g (Fin.last m)).2 s' : ℝ) * f s' := by
  have h1 : ∫ p, f p.1 ∂(mdpStepKernel M μ0 π (m + 1) g)
      = ∫ s, (∫ _a, f s ∂(π.select (m + 1) (g, s))) ∂(mdpStateKernel M μ0 (m + 1) g) :=
    ProbabilityTheory.integral_compProd Integrable.of_finite
  rw [h1]
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  rw [mdpStateKernel, Kernel.comap_apply]
  show ∫ s, f s ∂((M.transitionDist (g (Fin.last m)).1 (g (Fin.last m)).2).toMeasure) = _
  rw [integral_stateDist]
  rfl

/-- The exponential supermartingale: the capped sum is sub-Gaussian with the
number of active steps as its variance proxy. -/
lemma exp_supermartingale (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m : ℕ) (lam : ℝ) (N : ℕ) :
    ∫ h, Real.exp (lam * Wsum M s0 a0 Asub m h - lam ^ 2 / 8 * Cntr s0 a0 m h)
        ∂(mdpMeasure M μ0 π N) ≤ 1 := by
  classical
  induction N with
  | zero =>
      rw [mdpMeasure, integral_dirac]
      rw [Wsum_zero, Cntr_zero]
      simp
  | succ N ih =>
      rw [mdp_integral_trajectory_succ]
      refine le_trans (integral_mono Integrable.of_finite Integrable.of_finite
        (g := fun g ↦ Real.exp (lam * Wsum M s0 a0 Asub m g - lam ^ 2 / 8 * Cntr s0 a0 m g))
        fun g ↦ ?_) ih
      cases N with
      | zero =>
          have hW : ∀ p : Fin S × Fin A,
              Wsum M s0 a0 Asub m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) = 0 :=
            fun p ↦ Wsum_one M s0 a0 Asub m _
          have hC : ∀ p : Fin S × Fin A,
              Cntr s0 a0 m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p) = 0 :=
            fun p ↦ Cntr_one s0 a0 m _
          simp only [hW, hC, Wsum_zero, Cntr_zero]
          simp
      | succ K =>
          set av := actv s0 a0 m g K with hav
          set C := Real.exp (lam * Wsum M s0 a0 Asub m g - lam ^ 2 / 8 * Cntr s0 a0 m g) with hC
          have hCpos : 0 < C := Real.exp_pos _
          have hrw : ∀ p : Fin S × Fin A,
              Real.exp (lam * Wsum M s0 a0 Asub m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p)
                  - lam ^ 2 / 8 * Cntr s0 a0 m (Fin.snoc (α := fun _ ↦ Fin S × Fin A) g p))
                = (C * Real.exp (-(lam ^ 2 / 8) * av))
                    * Real.exp (lam * av * chiq M s0 a0 Asub p.1) := by
            intro p
            rw [Wsum_snoc, Cntr_snoc, hC, ← hav, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          simp_rw [hrw]
          rw [integral_const_mul, integral_step_fst M μ0 π K g
            (fun s' ↦ Real.exp (lam * av * chiq M s0 a0 Asub s'))]
          have hav01 : av = 0 ∨ (av = 1 ∧ g (Fin.last K) = (s0, a0)) := by
            simp only [hav, actv, dif_pos (show K < K + 1 by omega)]
            by_cases hcase : g ⟨K, by omega⟩ = (s0, a0) ∧ mdpVisitCount g K s0 a0 < m
            · right
              exact ⟨if_pos hcase, hcase.1⟩
            · left
              exact if_neg hcase
          rcases hav01 with h0 | ⟨h1, hg⟩
          · rw [h0]
            simp only [mul_zero, Real.exp_zero, mul_one, zero_mul]
            rw [row_sum_one M _ _, mul_one]
          · rw [h1, hg]
            simp only [mul_one, one_mul]
            calc C * Real.exp (-(lam ^ 2 / 8))
                  * ∑ s', (M.P s0 a0 s' : ℝ) * Real.exp (lam * chiq M s0 a0 Asub s')
                ≤ C * Real.exp (-(lam ^ 2 / 8)) * Real.exp (lam ^ 2 / 8) := by
                  refine mul_le_mul_of_nonneg_left (mgf_chiq_le M s0 a0 Asub lam) ?_
                  positivity
              _ = C := by
                  rw [mul_assoc, ← Real.exp_add]
                  simp

end Emp

namespace Emp
variable {S A : ℕ}

lemma visitCount_lt {N : ℕ} (h : MDPTrajectory S A N) (s0 : Fin S) (a0 : Fin A)
    (t t' : ℕ) (htt' : t < t') (ht : t < N) (hvis : h ⟨t, ht⟩ = (s0, a0)) :
    mdpVisitCount h t s0 a0 < mdpVisitCount h t' s0 a0 := by
  classical
  simp only [mdpVisitCount]
  refine Finset.card_lt_card ⟨fun i hi ↦ ?_, fun hsub ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨by omega, hi.2⟩
  · have hmem : (⟨t, ht⟩ : Fin N)
        ∈ Finset.univ.filter (fun i : Fin N ↦ i.val < t' ∧ h i = (s0, a0)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨htt', hvis⟩
    have := hsub hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    omega

lemma Cntr_le (s0 : Fin S) (a0 : Fin A) (m : ℕ) {N : ℕ} (h : MDPTrajectory S A N) :
    Cntr s0 a0 m h ≤ (m : ℝ) := by
  classical
  set g : ℕ → ℝ := fun t ↦ if t + 1 < N then actv s0 a0 m h t else 0 with hg
  set T := (Finset.range N).filter (fun t ↦ g t = 1) with hT
  have hg01 : ∀ t, g t = 0 ∨ g t = 1 := by
    intro t
    simp only [hg, actv]
    split
    · split
      · split
        · right; rfl
        · left; rfl
      · left; rfl
    · left; rfl
  have hsum : Cntr s0 a0 m h = (T.card : ℝ) := by
    simp only [Cntr, ← hg, hT, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rcases hg01 t with h0 | h1
    · rw [h0, if_neg (by norm_num)]
    · rw [h1, if_pos rfl]
  rw [hsum]
  have hvis : ∀ u : ℕ, u ∈ T → ∃ hu : u < N, h ⟨u, hu⟩ = (s0, a0)
      ∧ mdpVisitCount h u s0 a0 < m := by
    intro u hu
    obtain ⟨huR, hgu⟩ := Finset.mem_filter.1 hu
    have huN : u < N := Finset.mem_range.1 huR
    refine ⟨huN, ?_⟩
    simp only [hg] at hgu
    by_cases h1 : u + 1 < N
    · rw [if_pos h1] at hgu
      simp only [actv, dif_pos huN] at hgu
      by_cases hc : h ⟨u, huN⟩ = (s0, a0) ∧ mdpVisitCount h u s0 a0 < m
      · exact hc
      · rw [if_neg hc] at hgu; norm_num at hgu
    · rw [if_neg h1] at hgu; norm_num at hgu
  have hcard : T.card ≤ m := by
    have hle := Finset.card_le_card_of_injOn (f := fun t ↦ mdpVisitCount h t s0 a0)
      (s := T) (t := Finset.range m) ?_ ?_
    · simpa using hle
    · intro t ht
      obtain ⟨htN, -, hlt⟩ := hvis t ht
      simpa using hlt
    · intro t ht t' ht' heq
      obtain ⟨htN, htv, -⟩ := hvis t ht
      obtain ⟨ht'N, ht'v, -⟩ := hvis t' ht'
      rcases lt_trichotomy t t' with hlt | heqt | hgt
      · exact absurd heq (Nat.ne_of_lt (visitCount_lt h s0 a0 t t' hlt htN htv))
      · exact heqt
      · exact absurd heq.symm (Nat.ne_of_lt (visitCount_lt h s0 a0 t' t hgt ht'N ht'v))
  exact_mod_cast hcard

end Emp

namespace Emp
variable {S A : ℕ}

lemma hasSubgaussian_W (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m N : ℕ) :
    HasSubgaussianMGF (Wsum M s0 a0 Asub m) ((m : ℝ≥0) / 4) (mdpMeasure M μ0 π N) := by
  constructor
  · intro t
    exact Integrable.of_finite
  · intro t
    have hpt : ∀ h : MDPTrajectory S A N, Real.exp (t * Wsum M s0 a0 Asub m h)
        ≤ Real.exp (t ^ 2 * m / 8)
            * Real.exp (t * Wsum M s0 a0 Asub m h - t ^ 2 / 8 * Cntr s0 a0 m h) := by
      intro h
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hle := Cntr_le s0 a0 m h
      nlinarith [sq_nonneg t]
    have hcoe : (((m : ℝ≥0) / 4 : ℝ≥0) : ℝ) = (m : ℝ) / 4 := by push_cast; ring
    calc mgf (Wsum M s0 a0 Asub m) (mdpMeasure M μ0 π N) t
        = ∫ h, Real.exp (t * Wsum M s0 a0 Asub m h) ∂(mdpMeasure M μ0 π N) := rfl
      _ ≤ ∫ h, Real.exp (t ^ 2 * m / 8)
            * Real.exp (t * Wsum M s0 a0 Asub m h - t ^ 2 / 8 * Cntr s0 a0 m h)
            ∂(mdpMeasure M μ0 π N) :=
          integral_mono Integrable.of_finite Integrable.of_finite hpt
      _ = Real.exp (t ^ 2 * m / 8)
            * ∫ h, Real.exp (t * Wsum M s0 a0 Asub m h - t ^ 2 / 8 * Cntr s0 a0 m h)
              ∂(mdpMeasure M μ0 π N) := integral_const_mul _ _
      _ ≤ Real.exp (t ^ 2 * m / 8) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          exact exp_supermartingale M μ0 π s0 a0 Asub m t N
      _ = Real.exp ((((m : ℝ≥0) / 4 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
          rw [mul_one, hcoe]
          congr 1
          ring

lemma tail_W (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m N : ℕ) (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    (mdpMeasure M μ0 π N).real {h | (m : ℝ) * ε / 2 ≤ Wsum M s0 a0 Asub m h}
      ≤ Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  have hx : (0 : ℝ) ≤ (m : ℝ) * ε / 2 := by positivity
  have := (hasSubgaussian_W M μ0 π s0 a0 Asub m N).measure_ge_le hx
  refine le_trans this (le_of_eq ?_)
  congr 1
  have hcoe : (((m : ℝ≥0) / 4 : ℝ≥0) : ℝ) = (m : ℝ) / 4 := by push_cast; ring
  rw [hcoe]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp
  ring

end Emp

namespace Emp
variable {S A : ℕ}

/-- The successor state of a round, with a junk value when it was not observed. -/
noncomputable def succState (s0 : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (i : Fin n) : Fin S :=
  (mdpSuccessor h i).getD s0

lemma succState_eq (s0 : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (i : Fin n)
    (hi : i.val + 1 < n) : succState s0 h i = (h ⟨i.val + 1, hi⟩).1 := by
  simp [succState, mdpSuccessor, hi]

lemma succ_eq_some (s0 : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (i : Fin n)
    (hi : i.val + 1 < n) : mdpSuccessor h i = some (succState s0 h i) := by
  simp [succState, mdpSuccessor, hi]

/-- The observed count is the number of rounds playing `(s₀, a₀)` whose successor
has been recorded. -/
lemma observedCount_eq_card (s0 : Fin S) (a0 : Fin A) {n : ℕ} (h : MDPTrajectory S A n)
    (k : ℕ) (hk : k ≤ n) :
    mdpObservedCount h k s0 a0
      = (Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0))).card := by
  classical
  simp only [mdpObservedCount, mdpTransitionCount]
  rw [← Finset.card_biUnion]
  · congr 1
    ext i
    constructor
    · intro hi
      obtain ⟨s', -, hmem⟩ := Finset.mem_biUnion.1 hi
      obtain ⟨-, hi1, hi2, hi3⟩ := Finset.mem_filter.1 hmem
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1, hi2⟩
    · intro hi
      obtain ⟨-, hi1, hi2⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_biUnion.2 ⟨succState s0 h i, Finset.mem_univ _,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1, hi2, succ_eq_some s0 h i (by omega)⟩⟩
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun i hix hiy ↦ ?_
    obtain ⟨-, -, -, h1⟩ := Finset.mem_filter.1 hix
    obtain ⟨-, -, -, h2⟩ := Finset.mem_filter.1 hiy
    exact hxy (Option.some_injective _ (h1.symm.trans h2))

end Emp

namespace Emp
variable {S A : ℕ}

/-- The first `m` visits to `(s₀, a₀)` are exactly the visits whose transition was
recorded before a time at which exactly `m` transitions had been observed. -/
lemma visits_eq (s0 : Fin S) (a0 : Fin A) (m : ℕ) {n : ℕ} (h : MDPTrajectory S A n)
    (k : ℕ) (hk : k ≤ n) (hobs : mdpObservedCount h k s0 a0 = m) :
    Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < n ∧ h i = (s0, a0)
        ∧ mdpVisitCount h i.val s0 a0 < m)
      = Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0)) := by
  classical
  set Vk := Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0)) with hVk
  have hcard : Vk.card = m := by
    rw [hVk, ← observedCount_eq_card s0 a0 h k hk, hobs]
  ext i
  constructor
  · intro hi
    obtain ⟨-, hi1, hi2, hi3⟩ := Finset.mem_filter.1 hi
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hi2⟩
    by_contra hcon
    have hsub : Vk ⊆ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val ∧ h j = (s0, a0)) := by
      intro j hj
      obtain ⟨-, hj1, hj2⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, hj2⟩
    have := Finset.card_le_card hsub
    rw [hcard] at this
    simp only [mdpVisitCount] at hi3
    omega
  · intro hi
    obtain ⟨-, hi1, hi2⟩ := Finset.mem_filter.1 hi
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, hi2, ?_⟩
    have hsub : Finset.univ.filter (fun j : Fin n ↦ j.val < i.val ∧ h j = (s0, a0))
        ⊆ Vk.erase i := by
      intro j hj
      obtain ⟨-, hj1, hj2⟩ := Finset.mem_filter.1 hj
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, hj2⟩⟩
      intro hje
      rw [hje] at hj1
      omega
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hi, hcard] at hle
    have hm : 0 < m := by
      rw [← hcard]
      exact Finset.card_pos.2 ⟨i, hi⟩
    simp only [mdpVisitCount]
    omega

lemma Wsum_eq_sum (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S))
    (m : ℕ) {n : ℕ} (h : MDPTrajectory S A n) :
    Wsum M s0 a0 Asub m h
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < n ∧ h i = (s0, a0)
          ∧ mdpVisitCount h i.val s0 a0 < m), chiq M s0 a0 Asub (succState s0 h i) := by
  classical
  rw [Finset.sum_filter]
  simp only [Wsum]
  rw [← Fin.sum_univ_eq_sum_range (f := fun t ↦ if ht : t + 1 < n then
      actv s0 a0 m h t * chiq M s0 a0 Asub ((h ⟨t + 1, ht⟩).1) else 0)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h1 : i.val + 1 < n
  · rw [dif_pos h1]
    simp only [actv, dif_pos i.isLt]
    have hii : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
    rw [hii, succState_eq s0 h i h1]
    by_cases hc : h i = (s0, a0) ∧ mdpVisitCount h i.val s0 a0 < m
    · rw [if_pos hc, if_pos ⟨h1, hc.1, hc.2⟩, one_mul]
    · rw [if_neg hc, if_neg (by tauto), zero_mul]
  · rw [dif_neg h1, if_neg (by tauto)]

lemma card_succ_mem (s0 : Fin S) (a0 : Fin A) (Asub : Finset (Fin S)) {n : ℕ}
    (h : MDPTrajectory S A n) (k : ℕ) (hk : k ≤ n) :
    ((Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0))).filter
        (fun i ↦ succState s0 h i ∈ Asub)).card
      = ∑ s' ∈ Asub, mdpTransitionCount h k s0 a0 s' := by
  classical
  simp only [mdpTransitionCount]
  rw [← Finset.card_biUnion]
  · congr 1
    ext i
    constructor
    · intro hi
      obtain ⟨hi0, hiA⟩ := Finset.mem_filter.1 hi
      obtain ⟨-, hi1, hi2⟩ := Finset.mem_filter.1 hi0
      exact Finset.mem_biUnion.2 ⟨succState s0 h i, hiA,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1, hi2, succ_eq_some s0 h i (by omega)⟩⟩
    · intro hi
      obtain ⟨s', hs'A, hmem⟩ := Finset.mem_biUnion.1 hi
      obtain ⟨-, hi1, hi2, hi3⟩ := Finset.mem_filter.1 hmem
      have : succState s0 h i = s' := by
        have := succ_eq_some s0 h i (by omega)
        exact Option.some_injective _ (this.symm.trans hi3)
      exact Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hi1, hi2⟩, this ▸ hs'A⟩
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 fun i hix hiy ↦ ?_
    obtain ⟨-, -, -, h1⟩ := Finset.mem_filter.1 hix
    obtain ⟨-, -, -, h2⟩ := Finset.mem_filter.1 hiy
    exact hxy (Option.some_injective _ (h1.symm.trans h2))

end Emp

namespace Emp
variable {S A : ℕ}

lemma transCount_via_visits (s0 : Fin S) (a0 : Fin A) {n : ℕ} (h : MDPTrajectory S A n)
    (k : ℕ) (s' : Fin S) :
    mdpTransitionCount h k s0 a0 s'
      = ((Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0))).filter
          (fun i ↦ mdpSuccessor h i = some s')).card := by
  classical
  simp only [mdpTransitionCount, Finset.filter_filter, and_assoc]

lemma Wsum_eq_transCount (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A)
    (Asub : Finset (Fin S)) (m : ℕ) {n : ℕ} (h : MDPTrajectory S A n)
    (k : ℕ) (hk : k ≤ n) (hobs : mdpObservedCount h k s0 a0 = m) :
    Wsum M s0 a0 Asub m h
      = (∑ s' ∈ Asub, (mdpTransitionCount h k s0 a0 s' : ℝ))
          - (m : ℝ) * ∑ s'' ∈ Asub, (M.P s0 a0 s'' : ℝ) := by
  classical
  rw [Wsum_eq_sum, visits_eq s0 a0 m h k hk hobs]
  simp only [chiq]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hc1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0)),
      (if succState s0 h i ∈ Asub then (1 : ℝ) else 0)
      = ((∑ s' ∈ Asub, mdpTransitionCount h k s0 a0 s' : ℕ) : ℝ) := by
    rw [← card_succ_mem s0 a0 Asub h k hk, Finset.card_filter]
    push_cast
    rfl
  have hc2 : (Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k ∧ h i = (s0, a0))).card
      = m := by rw [← observedCount_eq_card s0 a0 h k hk, hobs]
  rw [hc1, hc2]
  push_cast
  ring

lemma empiricalRow_eq_of_obs (s0 : Fin S) (a0 : Fin A) (m : ℕ) {n : ℕ}
    (h : MDPTrajectory S A n) (k1 k2 : ℕ) (hk1 : k1 ≤ n) (hk2 : k2 ≤ n)
    (ho1 : mdpObservedCount h k1 s0 a0 = m) (ho2 : mdpObservedCount h k2 s0 a0 = m) :
    mdpEmpiricalRow h k1 s0 a0 = mdpEmpiricalRow h k2 s0 a0 := by
  classical
  have hV : Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k1 ∧ h i = (s0, a0))
      = Finset.univ.filter (fun i : Fin n ↦ i.val + 1 < k2 ∧ h i = (s0, a0)) := by
    rw [← visits_eq s0 a0 m h k1 hk1 ho1, ← visits_eq s0 a0 m h k2 hk2 ho2]
  have htc : ∀ s', mdpTransitionCount h k1 s0 a0 s' = mdpTransitionCount h k2 s0 a0 s' := by
    intro s'
    rw [transCount_via_visits s0 a0 h k1 s', transCount_via_visits s0 a0 h k2 s', hV]
  simp only [mdpEmpiricalRow, ho1, ho2]
  by_cases h0 : m = 0
  · simp [h0]
  · rw [if_neg h0, if_neg h0]
    funext s'
    rw [htc s']

lemma empiricalRow_sum_one (s0 : Fin S) (a0 : Fin A) {n : ℕ} (h : MDPTrajectory S A n)
    (k : ℕ) : ∑ s', mdpEmpiricalRow h k s0 a0 s' = 1 := by
  classical
  simp only [mdpEmpiricalRow]
  split
  · simp
  · rename_i h0
    rw [← Finset.sum_div]
    rw [show ∑ s', (mdpTransitionCount h k s0 a0 s' : ℝ)
        = ((mdpObservedCount h k s0 a0 : ℕ) : ℝ) by
      rw [mdpObservedCount]; push_cast; rfl]
    field_simp

end Emp

namespace Emp
variable {S A : ℕ}

open Classical in
/-- The empirical row at a time when exactly `m` transitions out of `(s₀, a₀)` had
been observed, if there is such a time, and the true row otherwise. -/
noncomputable def phat (M : FiniteMDP S A) (s0 : Fin S) (a0 : Fin A) (m n : ℕ)
    (h : MDPTrajectory S A n) : Fin S → ℝ :=
  if hk : ∃ k, k ≤ n ∧ mdpObservedCount h k s0 a0 = m then
    mdpEmpiricalRow h hk.choose s0 a0
  else fun s' ↦ (M.P s0 a0 s' : ℝ)

end Emp

open Emp in
theorem solution (S A n : ℕ) (hS : 0 < S) (hA : 0 < A)
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A)
    (s : Fin S) (a : Fin A) (m : ℕ) (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    (mdpMeasure M μ0 π n).real
        {h | ∃ k ≤ n, mdpObservedCount h k s a = m ∧
              ε ≤ ∑ s', |mdpEmpiricalRow h k s a s' - (M.P s a s' : ℝ)|}
      ≤ 2 ^ S * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  classical
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · have : (mdpMeasure M μ0 π n).real
        {h | ∃ k ≤ n, mdpObservedCount h k s a = m ∧
              ε ≤ ∑ s', |mdpEmpiricalRow h k s a s' - (M.P s a s' : ℝ)|} ≤ 1 :=
      measureReal_le_one
    refine le_trans this ?_
    rw [← hε0]
    have h1 : (1 : ℝ) ≤ 2 ^ S := one_le_pow₀ (by norm_num)
    simpa using h1
  set p : Fin S → ℝ := fun s' ↦ (M.P s a s' : ℝ) with hp
  set P := phat M s a m n with hP
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hsub : {h : MDPTrajectory S A n | ∃ k ≤ n, mdpObservedCount h k s a = m ∧
        ε ≤ ∑ s', |mdpEmpiricalRow h k s a s' - (M.P s a s' : ℝ)|}
      ⊆ {h | ε ≤ ∑ s', |P h s' - p s'|} := by
    rintro h ⟨k, hk, hobs, hdev⟩
    have hex : ∃ k, k ≤ n ∧ mdpObservedCount h k s a = m := ⟨k, hk, hobs⟩
    have hPh : P h = mdpEmpiricalRow h k s a := by
      rw [hP, phat, dif_pos hex]
      exact empiricalRow_eq_of_obs s a m h hex.choose k hex.choose_spec.1 hk
        hex.choose_spec.2 hobs
    simp only [Set.mem_setOf_eq, hPh, hp]
    exact hdev
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  have hsum : ∀ h : MDPTrajectory S A n, ∑ s', P h s' = ∑ s', p s' := by
    intro h
    have hone : ∑ s', p s' = 1 := row_sum_one M s a
    rw [hone, hP, phat]
    split
    · exact empiricalRow_sum_one s a h _
    · exact row_sum_one M s a
  have hbound : ∀ A' : Finset (Fin S),
      (mdpMeasure M μ0 π n).real {h | ε / 2 ≤ ∑ s' ∈ A', (P h s' - p s')}
        ≤ Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
    intro A'
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (tail_W M μ0 π s a A' m n hm hε)
    intro h hh
    simp only [Set.mem_setOf_eq] at hh ⊢
    by_cases hex : ∃ k, k ≤ n ∧ mdpObservedCount h k s a = m
    · have hk := hex.choose_spec.1
      have hobs := hex.choose_spec.2
      have hPh : P h = mdpEmpiricalRow h hex.choose s a := by rw [hP, phat, dif_pos hex]
      have hkey : Wsum M s a A' m h = (m : ℝ) * ∑ s' ∈ A', (P h s' - p s') := by
        rw [Wsum_eq_transCount M s a A' m h hex.choose hk hobs, hPh,
          Finset.sum_sub_distrib, mul_sub]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ ↦ ?_
        simp only [mdpEmpiricalRow, hobs]
        rw [if_neg (by omega)]
        field_simp
      rw [hkey]
      nlinarith [hh, hmr]
    · exfalso
      have hPh : P h = p := by rw [hP, phat, dif_neg hex]
      rw [hPh] at hh
      simp only [sub_self, Finset.sum_const_zero] at hh
      linarith
  have := BanditAlgorithm.l1_deviation_union_bound (μ := mdpMeasure M μ0 π n) P p ε
    (Real.exp (-(m : ℝ) * ε ^ 2 / 2)) hsum hbound
  simpa using this
