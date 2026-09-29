-- Prove2me | solution 1 for BanditAlgorithm.bandit_minimax_gaussian_pair_regret_sum_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-26T02:00:14.526831+00:00
-- url     : https://prove2.me/submissions/21943945-b02f-4a59-a648-62ce0e3ba583

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
import Theorems.Thm_BanditAlgorithm_gaussian_relative_entropy_formula
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Definitions.Def_GaussianBandit
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory InformationTheory
open BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), proof of Theorem 15.2,
printed pp. 199--201 / PDF pp. 208--210.  The proof below follows the source:
choose a least-pulled nonbaseline arm, compare the Gaussian environments
`(Δ,0,…,0)` and `(Δ,0,…,2Δ,…,0)`, apply Eq. (15.3),
Bretagnolle--Huber and Lemma 15.1, and tune
`Δ = sqrt ((k-1)n) / (2n)`.
-/

private theorem measurable_armPullCount_pair {k n : ℕ} (i : Fin k) :
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
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem pull_count_sum_pair {k n : ℕ} (h : BanditHistory k n) :
    ∑ i, (armPullCount i h : ℝ) = n := by
  rw [show (∑ i, (armPullCount i h : ℝ)) =
      ∑ i, ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm]
  rw [Finset.sum_comm]
  simp

private theorem gaussian_bandit_mean_pair {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μ) i = μ i := by
  simp [banditArmMean, gaussianBandit]

private theorem gaussian_bandit_integrable_pair {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) :
    Integrable id ((gaussianBandit μ).P i) := by
  apply memLp_one_iff_integrable.mp
  simpa [gaussianBandit] using
    (ProbabilityTheory.memLp_id_gaussianReal'
      (μ := μ i) (v := (1 : NNReal)) (1 : ENNReal) (by simp))

private theorem arm_pull_count_integrable_pair {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  have hprod := Integrable.bdd_mul
    (integrable_const (μ := banditMeasure ν π n) (1 : ℝ))
    (measurable_armPullCount_pair (n := n) i).aestronglyMeasurable
    (c := (n : ℝ)) (by
      filter_upwards [] with h
      rw [norm_natCast]
      exact_mod_cast (show armPullCount i h ≤ n by
        rw [armPullCount]
        simpa using (Finset.card_le_univ {t | ((h t).1 = i)}.toFinset)))
  simpa only [mul_one] using hprod

private theorem integral_ge_const_mul_measureReal
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f P) (hc : 0 ≤ c)
    (hfc : ∀ ω ∈ A, c ≤ f ω) (hf0 : ∀ ω, 0 ≤ f ω) :
    P.real A * c ≤ ∫ ω, f ω ∂P := by
  have hi : Integrable (A.indicator (fun _ : Ω ↦ c)) P :=
    (integrable_const c).indicator hA
  have hmono :
      ∫ ω, A.indicator (fun _ : Ω ↦ c) ω ∂P ≤ ∫ ω, f ω ∂P := by
    apply integral_mono hi hf
    intro ω
    by_cases hω : ω ∈ A
    · simpa [Set.indicator_of_mem hω] using hfc ω hω
    · simpa [Set.indicator, hω] using hf0 ω
  simpa [integral_indicator_const, hA, smul_eq_mul] using hmono

private theorem gaussian_optimal_mean_eq_pair {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) (hmax : ∀ j, μ j ≤ μ i) :
    banditOptimalMean (gaussianBandit μ) = μ i := by
  letI : Nonempty (Fin k) := ⟨i⟩
  rw [banditOptimalMean]
  simp only [gaussian_bandit_mean_pair]
  apply le_antisymm
  · exact ciSup_le hmax
  · exact le_ciSup (Set.finite_range μ).bddAbove i

private theorem gaussian_two_environment_pair_bound
    {k n : ℕ} (hk : 1 < k) (π : BanditPolicy k)
    (Δ : ℝ) (hΔ : Δ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ∃ μ μ' : Fin k → ℝ,
      (∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, μ' i ∈ Set.Icc (0 : ℝ) 1) ∧
      (n : ℝ) * Δ / 4 *
          Real.exp (-(2 * (n : ℝ) * Δ ^ 2 / ((k : ℝ) - 1))) ≤
        banditRegret (gaussianBandit μ) π n +
          banditRegret (gaussianBandit μ') π n := by
  classical
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, hk⟩
  let arms : Finset (Fin k) := Finset.univ.erase z
  have ho_ne : o ≠ z := by
    intro h
    have := congrArg Fin.val h
    simp [o, z] at this
  have harms : arms.Nonempty := by
    refine ⟨o, ?_⟩
    simp [arms, ho_ne]
  let μ : Fin k → ℝ := fun j ↦ if j = z then Δ else 0
  have hμbox : ∀ j, μ j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    by_cases hj : j = z
    · simp [μ, hj, hΔ.1, hΔ.2.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    · simp [μ, hj]
  have hopt : banditOptimalMean (gaussianBandit μ) = Δ := by
    apply gaussian_optimal_mean_eq_pair μ z
    intro j
    by_cases hj : j = z <;> simp [μ, hj, hΔ.1]
  have hgap (j : Fin k) :
      banditGap (gaussianBandit μ) j = if j = z then 0 else Δ := by
    rw [banditGap, hopt, gaussian_bandit_mean_pair]
    by_cases hj : j = z <;> simp [μ, hj]
  let pullMean : Fin k → ℝ := fun j ↦
    ∫ h, (armPullCount j h : ℝ) ∂banditMeasure (gaussianBandit μ) π n
  have hpull_nonneg (j : Fin k) : 0 ≤ pullMean j := by
    dsimp [pullMean]
    exact integral_nonneg (fun h ↦ by positivity)
  have htotal : (∑ j, pullMean j) = n := by
    simpa [pullMean] using
      (bandit_canonical_occupation_identities (gaussianBandit μ)
        (gaussian_bandit_integrable_pair μ) π n).2
  obtain ⟨i, hiarms, hmin⟩ := arms.exists_min_image pullMean harms
  have hiz : i ≠ z := by
    simpa [arms] using (Finset.mem_erase.mp hiarms).1
  have hsum_arms : (∑ j ∈ arms, pullMean j) ≤ n := by
    have hsplit :
        (∑ j ∈ arms, pullMean j) + pullMean z = n := by
      rw [← htotal]
      simpa [arms] using
        (Finset.sum_erase_add (f := pullMean) (Finset.mem_univ z))
    linarith [hpull_nonneg z]
  have hcard : (arms.card : ℝ) = (k : ℝ) - 1 := by
    simp [arms, Nat.cast_sub (by omega : 1 ≤ k)]
  have havg : (arms.card : ℝ) * pullMean i ≤
      ∑ j ∈ arms, pullMean j := by
    calc
      (arms.card : ℝ) * pullMean i = ∑ _j ∈ arms, pullMean i := by simp
      _ ≤ ∑ j ∈ arms, pullMean j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmin j hj
  have hk0 : 0 < (k : ℝ) - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hEi : pullMean i ≤ (n : ℝ) / ((k : ℝ) - 1) := by
    apply (le_div_iff₀ hk0).2
    rw [← hcard]
    calc
      pullMean i * (arms.card : ℝ) =
          (arms.card : ℝ) * pullMean i := by ring
      _ ≤ ∑ j ∈ arms, pullMean j := havg
      _ ≤ n := hsum_arms
  let μ' : Fin k → ℝ := fun j ↦ if j = i then 2 * Δ else μ j
  have hμ'box : ∀ j, μ' j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    by_cases hj : j = i
    · simp [μ', hj, hΔ.1]
      linarith [hΔ.2]
    · simpa [μ', hj] using hμbox j
  have hopt' : banditOptimalMean (gaussianBandit μ') = 2 * Δ := by
    calc
      banditOptimalMean (gaussianBandit μ') = μ' i := by
        apply gaussian_optimal_mean_eq_pair μ' i
        intro j
        rw [show μ' i = 2 * Δ by simp [μ']]
        by_cases hji : j = i
        · simp [μ', hji]
        · rw [show μ' j = μ j by simp [μ', hji]]
          by_cases hjz : j = z
          · simp [μ, hjz]
            linarith [hΔ.1]
          · simp [μ, hjz, hΔ.1]
      _ = 2 * Δ := by simp [μ']
  have hgap' (j : Fin k) :
      banditGap (gaussianBandit μ') j =
        if j = i then 0 else if j = z then Δ else 2 * Δ := by
    rw [banditGap, hopt', gaussian_bandit_mean_pair]
    by_cases hji : j = i
    · simp [μ', hji]
    · rw [show μ' j = μ j by simp [μ', hji]]
      by_cases hjz : j = z
      · subst j
        simp [μ, Ne.symm hiz]
        ring
      · simp [μ, hji, hjz]
  have hkl_arm (j : Fin k) :
      klDiv ((gaussianBandit μ).P j) ((gaussianBandit μ').P j) =
        if j = i then ENNReal.ofReal (2 * Δ ^ 2) else 0 := by
    change klDiv (gaussianReal (μ j) 1) (gaussianReal (μ' j) 1) = _
    rw [gaussian_relative_entropy_formula (μ j) (μ' j) (by norm_num)]
    by_cases hj : j = i
    · subst j
      rw [if_pos rfl]
      have hmui : μ i = 0 := by simp [μ, hiz]
      have hmupi : μ' i = 2 * Δ := by simp [μ']
      rw [hmui, hmupi]
      congr 1
      norm_num
      ring
    · rw [if_neg hj]
      have hmueq : μ' j = μ j := by simp [μ', hj]
      rw [hmueq]
      simp
  have hKLfinite (j : Fin k) :
      klDiv ((gaussianBandit μ).P j) ((gaussianBandit μ').P j) ≠ ⊤ := by
    rw [hkl_arm]
    split
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hdiv := bandit_divergence_decomposition
    (gaussianBandit μ) (gaussianBandit μ') hKLfinite π n
  have hDtoReal :
      (klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n)).toReal =
          pullMean i * (2 * Δ ^ 2) := by
    rw [hdiv]
    simp only [hkl_arm]
    rw [show (∑ j, ENNReal.ofReal
          (∫ h, (armPullCount j h : ℝ)
            ∂banditMeasure (gaussianBandit μ) π n) *
          (if j = i then ENNReal.ofReal (2 * Δ ^ 2) else 0)) =
        ENNReal.ofReal (pullMean i) * ENNReal.ofReal (2 * Δ ^ 2) by
      simp [pullMean]]
    rw [← ENNReal.ofReal_mul (hpull_nonneg i)]
    rw [ENNReal.toReal_ofReal]
    positivity
  have hDfinite :
      klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n) ≠ ⊤ := by
    rw [hdiv]
    apply ENNReal.sum_ne_top.2
    intro j hj
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKLfinite j)
  have hDle :
      (klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n)).toReal ≤
          2 * (n : ℝ) * Δ ^ 2 / ((k : ℝ) - 1) := by
    rw [hDtoReal]
    have hsq : 0 ≤ 2 * Δ ^ 2 := by positivity
    calc
      pullMean i * (2 * Δ ^ 2) ≤
          ((n : ℝ) / ((k : ℝ) - 1)) * (2 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_right hEi hsq
      _ = 2 * (n : ℝ) * Δ ^ 2 / ((k : ℝ) - 1) := by
        field_simp [ne_of_gt hk0]
  let P := banditMeasure (gaussianBandit μ) π n
  let Q := banditMeasure (gaussianBandit μ') π n
  let A : Set (BanditHistory k n) :=
    {h | (armPullCount z h : ℝ) ≤ (n : ℝ) / 2}
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_armPullCount_pair z) measurable_const
  have hBH :
      (1 / 2 : ℝ) * Real.exp (-(klDiv P Q).toReal) ≤
        P.real A + Q.real Aᶜ := by
    simpa [P, Q] using
      (bretagnolle_huber_inequality
        (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n) hA hDfinite)
  have hregP : banditRegret (gaussianBandit μ) π n =
      Δ * ∑ j ∈ arms, pullMean j := by
    rw [bandit_regret_decomposition (gaussianBandit μ)
      (gaussian_bandit_integrable_pair μ) π n]
    simp only [hgap, pullMean]
    rw [show (∑ j, (if j = z then 0 else Δ) *
          ∫ h, (armPullCount j h : ℝ)
            ∂banditMeasure (gaussianBandit μ) π n) =
        ∑ j ∈ arms, Δ *
          ∫ h, (armPullCount j h : ℝ)
            ∂banditMeasure (gaussianBandit μ) π n by
      let f : Fin k → ℝ := fun j ↦ (if j = z then 0 else Δ) *
        ∫ h, (armPullCount j h : ℝ)
          ∂banditMeasure (gaussianBandit μ) π n
      have hfz : f z = 0 := by simp [f]
      change (∑ j, f j) = _
      rw [← Finset.sum_erase Finset.univ hfz]
      apply Finset.sum_congr
      · rfl
      · intro j hj
        have hjz : j ≠ z := (Finset.mem_erase.mp hj).1
        simp [f, hjz, arms]]
    rw [← Finset.mul_sum]
  have hIntSumP :
      Integrable
        (fun h : BanditHistory k n ↦
          ∑ j ∈ arms, (armPullCount j h : ℝ)) P := by
    dsimp [P]
    exact integrable_finset_sum arms fun j hj ↦
      arm_pull_count_integrable_pair (gaussianBandit μ) π j
  have hIntFP :
      Integrable
        (fun h : BanditHistory k n ↦
          Δ * ∑ j ∈ arms, (armPullCount j h : ℝ)) P :=
    hIntSumP.const_mul Δ
  have hPevent :
      P.real A * (Δ * (n : ℝ) / 2) ≤
        banditRegret (gaussianBandit μ) π n := by
    have hlower :
        P.real A * (Δ * (n : ℝ) / 2) ≤
          ∫ h, Δ * ∑ j ∈ arms, (armPullCount j h : ℝ) ∂P := by
      apply integral_ge_const_mul_measureReal P hA
        (fun h : BanditHistory k n ↦
          Δ * ∑ j ∈ arms, (armPullCount j h : ℝ))
        (Δ * (n : ℝ) / 2) hIntFP
      · exact div_nonneg (mul_nonneg hΔ.1 (Nat.cast_nonneg n)) (by norm_num)
      · intro h hh
        have hzle : (armPullCount z h : ℝ) ≤ (n : ℝ) / 2 := hh
        have hsplit :
            (∑ j ∈ arms, (armPullCount j h : ℝ)) +
                (armPullCount z h : ℝ) = n := by
          rw [← pull_count_sum_pair h]
          simpa [arms] using
            (Finset.sum_erase_add
              (f := fun j ↦ (armPullCount j h : ℝ))
              (Finset.mem_univ z))
        have : (n : ℝ) / 2 ≤
            ∑ j ∈ arms, (armPullCount j h : ℝ) := by linarith
        convert mul_le_mul_of_nonneg_left this hΔ.1 using 1 <;> ring
      · intro h
        exact mul_nonneg hΔ.1 (by positivity)
    calc
      _ ≤ ∫ h, Δ * ∑ j ∈ arms, (armPullCount j h : ℝ) ∂P := hlower
      _ = Δ * ∑ j ∈ arms, pullMean j := by
        dsimp [P]
        rw [integral_const_mul]
        rw [integral_finset_sum]
        intro j hj
        exact arm_pull_count_integrable_pair (gaussianBandit μ) π j
      _ = banditRegret (gaussianBandit μ) π n := hregP.symm
  let pullMean' : Fin k → ℝ := fun j ↦
    ∫ h, (armPullCount j h : ℝ) ∂Q
  have hpull_nonneg' (j : Fin k) : 0 ≤ pullMean' j := by
    dsimp [pullMean', Q]
    exact integral_nonneg (fun h ↦ by positivity)
  have hregQlower :
      Δ * pullMean' z ≤ banditRegret (gaussianBandit μ') π n := by
    rw [bandit_regret_decomposition (gaussianBandit μ')
      (gaussian_bandit_integrable_pair μ') π n]
    have hterm :
        banditGap (gaussianBandit μ') z * pullMean' z ≤
          ∑ j, banditGap (gaussianBandit μ') j * pullMean' j := by
      have ht := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j ↦ banditGap (gaussianBandit μ') j * pullMean' j)
        (fun j hj ↦ mul_nonneg (by
          rw [hgap']
          split
          · exact le_rfl
          · split
            · exact hΔ.1
            · exact mul_nonneg (by norm_num) hΔ.1) (hpull_nonneg' j))
        (Finset.mem_univ z)
      simpa using ht
    have hznoti : z ≠ i := Ne.symm hiz
    simpa [pullMean', Q, hgap', hznoti] using hterm
  have hIntFQ :
      Integrable
        (fun h : BanditHistory k n ↦ Δ * (armPullCount z h : ℝ)) Q := by
    dsimp [Q]
    exact (arm_pull_count_integrable_pair (gaussianBandit μ') π z).const_mul Δ
  have hQevent :
      Q.real Aᶜ * (Δ * (n : ℝ) / 2) ≤
        banditRegret (gaussianBandit μ') π n := by
    have hlower :
        Q.real Aᶜ * (Δ * (n : ℝ) / 2) ≤
          ∫ h, Δ * (armPullCount z h : ℝ) ∂Q := by
      apply integral_ge_const_mul_measureReal Q hA.compl
        (fun h : BanditHistory k n ↦ Δ * (armPullCount z h : ℝ))
        (Δ * (n : ℝ) / 2) hIntFQ
      · exact div_nonneg (mul_nonneg hΔ.1 (Nat.cast_nonneg n)) (by norm_num)
      · intro h hh
        have hzgt : (n : ℝ) / 2 < (armPullCount z h : ℝ) := by
          simpa [A] using hh
        convert mul_le_mul_of_nonneg_left hzgt.le hΔ.1 using 1 <;> ring
      · intro h
        exact mul_nonneg hΔ.1 (by positivity)
    calc
      _ ≤ ∫ h, Δ * (armPullCount z h : ℝ) ∂Q := hlower
      _ = Δ * pullMean' z := by
        rw [integral_const_mul]
      _ ≤ banditRegret (gaussianBandit μ') π n := hregQlower
  have hexp :
      Real.exp (-(2 * (n : ℝ) * Δ ^ 2 / ((k : ℝ) - 1))) ≤
        Real.exp (-(klDiv P Q).toReal) := by
    apply Real.exp_le_exp.mpr
    simpa [P, Q] using neg_le_neg hDle
  have hc : 0 ≤ Δ * (n : ℝ) / 2 :=
    div_nonneg (mul_nonneg hΔ.1 (Nat.cast_nonneg n)) (by norm_num)
  have hprob :
      (1 / 2 : ℝ) *
          Real.exp (-(2 * (n : ℝ) * Δ ^ 2 / ((k : ℝ) - 1))) ≤
        P.real A + Q.real Aᶜ :=
    (mul_le_mul_of_nonneg_left hexp (by norm_num)).trans hBH
  refine ⟨μ, μ', hμbox, hμ'box, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_right hprob hc
  have hsum := add_le_add hPevent hQevent
  nlinarith

theorem solution {k n : ℕ} (hk : 1 < k) (hn : k - 1 ≤ n)
    (π : BanditPolicy k) :
    ∃ μ μ' : Fin k → ℝ,
      (∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, μ' i ∈ Set.Icc (0 : ℝ) 1) ∧
      2 * (Real.sqrt (((k : ℝ) - 1) * n) / 27) ≤
        banditRegret (gaussianBandit μ) π n +
          banditRegret (gaussianBandit μ') π n := by
  classical
  have hkNat : 1 ≤ k := by omega
  have hnNat : 0 < n := by omega
  have hkR : 0 < (k : ℝ) - 1 := by
    have hkR' : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hknR : (k : ℝ) - 1 ≤ (n : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hkNat]
    exact_mod_cast hn
  let S : ℝ := Real.sqrt (((k : ℝ) - 1) * n)
  let Δ : ℝ := S / (2 * n)
  have hprod : 0 < ((k : ℝ) - 1) * n := mul_pos hkR hnR
  have hSpos : 0 < S := by
    simpa [S] using Real.sqrt_pos.2 hprod
  have hSsq : S ^ 2 = ((k : ℝ) - 1) * n := by
    dsimp [S]
    exact Real.sq_sqrt hprod.le
  have hSn : S ≤ (n : ℝ) := by
    have hmul : ((k : ℝ) - 1) * n ≤ (n : ℝ) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (S - n)]
  have hΔpos : 0 < Δ := by
    dsimp [Δ]
    positivity
  have hΔle : Δ ≤ (1 / 2 : ℝ) := by
    dsimp [Δ]
    rw [div_le_iff₀ (mul_pos (by norm_num) hnR)]
    nlinarith
  obtain ⟨μ, μ', hμ, hμ', hsum⟩ :=
    gaussian_two_environment_pair_bound hk π Δ ⟨hΔpos.le, hΔle⟩
  have hcoef : (n : ℝ) * Δ / 4 = S / 8 := by
    dsimp [Δ]
    field_simp [ne_of_gt hnR]
    <;> ring
  have hexponent :
      2 * (n : ℝ) * Δ ^ 2 / ((k : ℝ) - 1) = (1 / 2 : ℝ) := by
    dsimp [Δ]
    rw [div_pow, hSsq]
    field_simp [ne_of_gt hnR, ne_of_gt hkR]
  have hexp : (16 / 27 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    calc
      (16 / 27 : ℝ) ≤ (1 - (1 / 2 : ℝ) / 6) ^ (6 : ℕ) := by norm_num
      _ ≤ Real.exp (-(1 / 2 : ℝ)) :=
        Real.one_sub_div_pow_le_exp_neg
          (n := 6) (t := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨μ, μ', hμ, hμ', ?_⟩
  rw [hcoef, hexponent] at hsum
  have hscale : S / 8 * (16 / 27 : ℝ) ≤
      S / 8 * Real.exp (-(1 / 2 : ℝ)) := by
    gcongr
  nlinarith
