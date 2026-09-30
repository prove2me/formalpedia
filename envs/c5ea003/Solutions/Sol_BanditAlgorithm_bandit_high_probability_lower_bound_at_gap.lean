-- Prove2me | solution 1 for BanditAlgorithm.bandit_high_probability_lower_bound_at_gap
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:03:59.586288+00:00
-- url     : https://prove2.me/submissions/36f73619-8000-4baa-8ca6-ceb56c9e144d

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
import Theorems.Thm_BanditAlgorithm_gaussian_relative_entropy_formula
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Definitions.Def_GaussianBandit
import Mathlib.Tactic

/-
Local measurable-count, Gaussian-mean, integrability and two-environment algebra
are adapted from the complete accepted proof by Harry_Xu,
theorem fa7b1426-1743-4773-bad5-c9471f4f47f9, submission 21943945-b02f-4a59-a648-62ce0e3ba583.
Original SHA-256: b8025f75267b13eda2234050753b3fb6624673ea3d47137d4f1de9c8447eb25e.
The assembly manifest records exact unchanged source selections.
Only registered theorem statements are imported; all reused auxiliary proofs are included.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open BanditAlgorithm

/-!
Historical source context: these local helpers and the two-environment algebra
come from an accepted proof of Lattimore--Szepesvari Theorem 15.2, which tunes
the gap to obtain a minimax expected-regret bound. The theorem proved in this
file is instead the fixed-gap testing core of Theorem 17.1 (pp. 216--217).
Here Delta remains the arbitrary supplied gap; no tuning step is performed.
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

theorem solution {k n : ℕ}
    (hk : 2 ≤ k) (hn : 1 ≤ n) {B : ℝ} (hB : 0 < B) (π : BanditPolicy k)
    (hbound : ∀ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      banditRegret (gaussianBandit μvec) π n ≤ B * Real.sqrt (((k : ℝ) - 1) * n))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (Δ : ℝ)
    (hΔpos : 0 < Δ) (hΔle : Δ ≤ 1 / 2)
    (htest : 2 * δ ≤ (1 / 2 : ℝ) *
      Real.exp (-2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)))) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      δ ≤ (banditMeasure (gaussianBandit μvec) π n).real
        {h | Δ * n / 2 ≤
          ∑ i, (armPullCount i h : ℝ) * banditGap (gaussianBandit μvec) i} := by
  have hk : 1 < k := by omega
  have hΔ : Δ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hΔpos.le, hΔle⟩
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
  obtain ⟨i, hiarms, hmin⟩ := arms.exists_min_image pullMean harms
  have hiz : i ≠ z := by
    simpa [arms] using (Finset.mem_erase.mp hiarms).1
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
  have hEi : pullMean i ≤
      B * Real.sqrt (((k : ℝ) - 1) * n) / (Δ * ((k : ℝ) - 1)) := by
    apply (le_div_iff₀ (mul_pos hΔpos hk0)).2
    calc
      pullMean i * (Δ * ((k : ℝ) - 1)) = Δ * ((arms.card : ℝ) * pullMean i) := by
        rw [hcard]
        ring
      _ ≤ Δ * ∑ j ∈ arms, pullMean j := mul_le_mul_of_nonneg_left havg hΔpos.le
      _ = banditRegret (gaussianBandit μ) π n := hregP.symm
      _ ≤ B * Real.sqrt (((k : ℝ) - 1) * n) := hbound μ hμbox

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
  have hroot : Real.sqrt (((k : ℝ) - 1) * n) / ((k : ℝ) - 1) =
      Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by
    calc
      Real.sqrt (((k : ℝ) - 1) * n) / ((k : ℝ) - 1) =
          Real.sqrt (n : ℝ) * (Real.sqrt ((k : ℝ) - 1) / ((k : ℝ) - 1)) := by
        rw [Real.sqrt_mul hk0.le]
        ring
      _ = Real.sqrt (n : ℝ) / Real.sqrt ((k : ℝ) - 1) := by
        rw [Real.sqrt_div_self']
        ring
      _ = Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) :=
        (Real.sqrt_div (Nat.cast_nonneg n) _).symm
  have hDle :
      (klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n)).toReal ≤
          2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by
    rw [hDtoReal]
    calc
      pullMean i * (2 * Δ ^ 2) ≤
          (B * Real.sqrt (((k : ℝ) - 1) * n) / (Δ * ((k : ℝ) - 1))) * (2 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_right hEi (by positivity)
      _ = 2 * B * Δ * (Real.sqrt (((k : ℝ) - 1) * n) / ((k : ℝ) - 1)) := by
        field_simp [hΔpos.ne', hk0.ne']
        <;> ring
      _ = 2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by rw [hroot]

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
  have hprob : 2 * δ ≤ P.real A + Q.real Aᶜ := by
    refine htest.trans ((mul_le_mul_of_nonneg_left ?_ (by norm_num)).trans hBH)
    apply Real.exp_le_exp.mpr
    have hd := neg_le_neg hDle
    simpa [P, Q] using hd
  by_cases hPA : δ ≤ P.real A
  · refine ⟨μ, hμbox, hPA.trans (measureReal_mono ?_)⟩
    intro h hh
    have hzle : (armPullCount z h : ℝ) ≤ (n : ℝ) / 2 := hh
    have hsplit : (∑ j ∈ arms, (armPullCount j h : ℝ)) +
        (armPullCount z h : ℝ) = n := by
      rw [← pull_count_sum_pair h]
      simpa [arms] using
        (Finset.sum_erase_add (f := fun j ↦ (armPullCount j h : ℝ)) (Finset.mem_univ z))
    have hhalf : (n : ℝ) / 2 ≤ ∑ j ∈ arms, (armPullCount j h : ℝ) := by linarith
    change Δ * n / 2 ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ) j
    calc
      Δ * n / 2 = Δ * ((n : ℝ) / 2) := by ring
      _ ≤ Δ * ∑ j ∈ arms, (armPullCount j h : ℝ) :=
        mul_le_mul_of_nonneg_left hhalf hΔpos.le
      _ = ∑ j ∈ arms, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjz : j ≠ z := (Finset.mem_erase.mp hj).1
        rw [hgap j, if_neg hjz]
        ring
      _ ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ) j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ arms)
        intro j hj hjout
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [hgap]
        split_ifs <;> positivity
  · have hQA : δ ≤ Q.real Aᶜ := by linarith [lt_of_not_ge hPA]
    refine ⟨μ', hμ'box, hQA.trans (measureReal_mono ?_)⟩
    intro h hh
    have hzgt : (n : ℝ) / 2 < (armPullCount z h : ℝ) := by simpa [A] using hh
    have hterm : (armPullCount z h : ℝ) * banditGap (gaussianBandit μ') z ≤
        ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin k => (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j)
        _ (Finset.mem_univ z)
      intro j hj
      apply mul_nonneg (Nat.cast_nonneg _)
      rw [hgap']
      split_ifs <;> positivity
    have hgapz : banditGap (gaussianBandit μ') z = Δ := by
      rw [hgap' z, if_neg (Ne.symm hiz), if_pos rfl]
    change Δ * n / 2 ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j
    calc
      Δ * n / 2 = ((n : ℝ) / 2) * Δ := by ring
      _ ≤ (armPullCount z h : ℝ) * Δ := mul_le_mul_of_nonneg_right hzgt.le hΔpos.le
      _ = (armPullCount z h : ℝ) * banditGap (gaussianBandit μ') z := by rw [hgapz]
      _ ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j := hterm

#print axioms solution
