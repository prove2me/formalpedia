-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_lower
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T02:18:46.539771+00:00
-- url     : https://prove2.me/submissions/5adfb83b-5823-45c3-9a4b-645037f223af

import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_bound
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
import Theorems.Thm_BanditAlgorithm_gaussian_relative_entropy_formula
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory InformationTheory
open Filter Topology

namespace BanditAlgorithm

private theorem measurable_armPullCount_lower {k n : ℕ} (i : Fin k) :
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
  intro t _
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem pull_count_sum_lower {k n : ℕ} (h : BanditHistory k n) :
    ∑ i, (armPullCount i h : ℝ) = n := by
  rw [show (∑ i, (armPullCount i h : ℝ)) =
      ∑ i, ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro i _
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

private theorem arm_pull_count_integrable_lower {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  have hprod := Integrable.bdd_mul
    (integrable_const (μ := banditMeasure ν π n) (1 : ℝ))
    (measurable_armPullCount_lower (n := n) i).aestronglyMeasurable
    (c := (n : ℝ)) (by
      filter_upwards [] with h
      rw [norm_natCast]
      exact_mod_cast (show armPullCount i h ≤ n by
        rw [armPullCount]
        simpa using
          (Finset.card_le_univ {t | ((h t).1 = i)}.toFinset)))
  simpa only [mul_one] using hprod

private theorem integral_ge_const_mul_measureReal_lower
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

private theorem gaussian_bandit_mean_lower {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μ) i = μ i := by
  simp [banditArmMean, gaussianBandit]

private theorem gaussian_optimal_mean_eq_lower {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) (hmax : ∀ j, μ j ≤ μ i) :
    banditOptimalMean (gaussianBandit μ) = μ i := by
  letI : Nonempty (Fin k) := ⟨i⟩
  rw [banditOptimalMean]
  simp only [gaussian_bandit_mean_lower]
  apply le_antisymm
  · exact ciSup_le hmax
  · exact le_ciSup (Set.finite_range μ).bddAbove i

private theorem tendsto_log_nat_lower :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_inv_log_nat_lower :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_lower

private theorem tendsto_log_log_nat_div_log_nat_lower :
    Tendsto
      (fun n : ℕ ↦
        Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.comp_tendsto
    tendsto_log_nat_lower).tendsto_div_nhds_zero

private theorem exists_positive_perturbation_lower {Δ a : ℝ}
    (hΔ : 0 < Δ) (ha : a < 2 / Δ ^ 2) :
    ∃ δ : ℝ, 0 < δ ∧ a < 2 / (Δ + δ) ^ 2 := by
  have hcont :
      Tendsto (fun δ : ℝ ↦ 2 / (Δ + δ) ^ 2)
        (𝓝 0) (𝓝 (2 / Δ ^ 2)) := by
    have hadd :
        Tendsto (fun δ : ℝ ↦ Δ + δ) (𝓝 0) (𝓝 Δ) := by
      simpa using
        (tendsto_const_nhds (x := Δ)).add
          (tendsto_id : Tendsto (fun δ : ℝ ↦ δ) (𝓝 0) (𝓝 0))
    have hinv := (hadd.pow 2).inv₀ (pow_ne_zero 2 (ne_of_gt hΔ))
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul hinv
  have hcoef : ∀ᶠ δ : ℝ in 𝓝 0, a < 2 / (Δ + δ) ^ 2 :=
    hcont.eventually (eventually_gt_nhds ha)
  have hcoef' : ∀ᶠ δ : ℝ in 𝓝[>] 0, a < 2 / (Δ + δ) ^ 2 :=
    hcoef.filter_mono inf_le_left
  have hpos' : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ :=
    self_mem_nhdsWithin
  rcases (hcoef'.and hpos').exists with ⟨δ, hcoefδ, hδ⟩
  exact ⟨δ, hδ, hcoefδ⟩

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k)
    (hπ : IsGaussianTSPolicy π) (i : Fin k)
    (hi : 0 < banditGap (gaussianBandit μvec) i) :
    ∀ a : ℝ, a < 2 / banditGap (gaussianBandit μvec) i ^ 2 →
      ∀ᶠ n : ℕ in Filter.atTop,
        a <
          (∫ h, (armPullCount i h : ℝ)
            ∂banditMeasure (gaussianBandit μvec) π n) /
              Real.log n := by
  classical
  intro a ha
  let ν := gaussianBandit μvec
  let Δ : ℝ := banditGap ν i
  have hΔ : 0 < Δ := by simpa [Δ, ν] using hi
  obtain ⟨δ, hδ, haδ⟩ :=
    exists_positive_perturbation_lower hΔ (by simpa [Δ, ν] using ha)
  let mstar : ℝ := banditOptimalMean ν
  let μ' : Fin k → ℝ := fun j ↦ if j = i then mstar + δ else μvec j
  let ν' := gaussianBandit μ'
  have hmean_le (j : Fin k) : μvec j ≤ mstar := by
    dsimp [mstar, ν]
    rw [banditOptimalMean]
    simpa only [gaussian_bandit_mean_lower] using
      (le_ciSup (Set.finite_range μvec).bddAbove j)
  have hμ'i : μ' i = mstar + δ := by simp [μ']
  have hopt' : banditOptimalMean ν' = mstar + δ := by
    change banditOptimalMean (gaussianBandit μ') = mstar + δ
    rw [gaussian_optimal_mean_eq_lower μ' i]
    · exact hμ'i
    · intro j
      by_cases hj : j = i
      · simp [μ', hj]
      · simp only [μ', hj, if_false, hμ'i]
        linarith [hmean_le j]
  have hgap' (j : Fin k) (hj : j ≠ i) :
      δ ≤ banditGap ν' j := by
    rw [banditGap, hopt']
    change δ ≤ mstar + δ - banditArmMean (gaussianBandit μ') j
    rw [gaussian_bandit_mean_lower]
    change δ ≤ mstar + δ - μ' j
    rw [show μ' j = μvec j by simp [μ', hj]]
    linarith [hmean_le j]
  have hgap'pos (j : Fin k) (hj : j ≠ i) :
      0 < banditGap ν' j :=
    hδ.trans_le (hgap' j hj)
  have hμi : μvec i = mstar - Δ := by
    dsimp [Δ, mstar, ν]
    rw [banditGap, gaussian_bandit_mean_lower]
    ring
  let d : ℝ := (Δ + δ) ^ 2 / 2
  have hd : 0 < d := by
    dsimp [d]
    have : 0 < Δ + δ := by linarith
    positivity
  obtain ⟨C, hC, hfinite⟩ := gaussian_ts_suboptimal_pull_count_bound
  let M : ℝ :=
    2 * C * (1 + 1 / Δ ^ 2) +
      2 * (k : ℝ) * C * (1 + 1 / δ ^ 2)
  have hM : 0 < M := by
    dsimp [M]
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    positivity
  let c₀ : ℝ := Real.log M - Real.log (1 / 2 : ℝ)
  let S : ℕ → ℝ := fun n ↦
    ((Real.log n - Real.log 2 - Real.log (Real.log n) - c₀) / d) /
      Real.log n
  have hS : Tendsto S atTop (𝓝 (1 / d)) := by
    have hconst (x : ℝ) :
        Tendsto (fun n : ℕ ↦ x / Real.log (n : ℝ))
          atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := x)).mul tendsto_inv_log_nat_lower
    have hinside :
        Tendsto
          (fun n : ℕ ↦
            1 - Real.log 2 / Real.log (n : ℝ) -
              Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) -
                c₀ / Real.log (n : ℝ))
          atTop (𝓝 1) := by
      have h :=
        (((tendsto_const_nhds (x := (1 : ℝ))).sub
          (hconst (Real.log 2))).sub
            tendsto_log_log_nat_div_log_nat_lower).sub (hconst c₀)
      simpa only [sub_zero] using h
    have hscaled :
        Tendsto
          (fun n : ℕ ↦ (1 / d) *
            (1 - Real.log 2 / Real.log (n : ℝ) -
              Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) -
                c₀ / Real.log (n : ℝ)))
          atTop (𝓝 (1 / d)) := by
      simpa using (tendsto_const_nhds (x := 1 / d)).mul hinside
    refine hscaled.congr' ?_
    filter_upwards [tendsto_log_nat_lower.eventually_gt_atTop 0] with n hn
    dsimp [S]
    field_simp [ne_of_gt hn, ne_of_gt hd]
  have haS : ∀ᶠ n : ℕ in atTop, a < S n :=
    hS.eventually (eventually_gt_nhds (by
      have hdform : 1 / d = 2 / (Δ + δ) ^ 2 := by
        dsimp [d]
        field_simp [ne_of_gt (by linarith : 0 < Δ + δ)]
      rwa [hdform]))
  filter_upwards [haS, tendsto_log_nat_lower.eventually_ge_atTop 1,
    eventually_atTop.2 ⟨2, fun n hn ↦ hn⟩] with n haSn hlog hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  let P := banditMeasure ν π n
  let Q := banditMeasure ν' π n
  let Ep : ℝ := ∫ h, (armPullCount i h : ℝ) ∂P
  have hEp0 : 0 ≤ Ep := by
    dsimp [Ep]
    exact integral_nonneg fun h ↦ by positivity
  have hEpUpper :
      Ep ≤ C * (1 + Real.log n / Δ ^ 2) := by
    dsimp [Ep, P, Δ, ν]
    exact hfinite k μvec π hπ i hi n hn
  let others : Finset (Fin k) := Finset.univ.erase i
  let EqOthers : ℝ :=
    ∫ h, ∑ j ∈ others, (armPullCount j h : ℝ) ∂Q
  have hIntQ (j : Fin k) :
      Integrable (fun h : BanditHistory k n ↦ (armPullCount j h : ℝ)) Q := by
    dsimp [Q]
    exact arm_pull_count_integrable_lower ν' π j
  have hEqOthers :
      EqOthers ≤ (k : ℝ) * C * (1 + Real.log n / δ ^ 2) := by
    rw [show EqOthers =
        ∑ j ∈ others,
          ∫ h, (armPullCount j h : ℝ) ∂Q by
      dsimp [EqOthers]
      rw [integral_finset_sum]
      intro j hj
      exact hIntQ j]
    calc
      (∑ j ∈ others,
          ∫ h, (armPullCount j h : ℝ) ∂Q) ≤
          ∑ _j ∈ others,
            C * (1 + Real.log n / δ ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hbase :
            (∫ h, (armPullCount j h : ℝ)
              ∂banditMeasure (gaussianBandit μ') π n) ≤
                C * (1 + Real.log n /
                  banditGap (gaussianBandit μ') j ^ 2) :=
          hfinite k μ' π hπ j
            (by simpa [ν'] using hgap'pos j hji) n hn
        have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
        have hg : 0 < banditGap ν' j := hgap'pos j hji
        have hsq : δ ^ 2 ≤ banditGap ν' j ^ 2 := by
          nlinarith [hgap' j hji]
        have hfrac :
            Real.log n / banditGap ν' j ^ 2 ≤
              Real.log n / δ ^ 2 :=
          div_le_div_of_nonneg_left (le_trans zero_le_one hlog) hδsq hsq
        have hscale :
            C * (1 + Real.log n / banditGap ν' j ^ 2) ≤
              C * (1 + Real.log n / δ ^ 2) := by
          nlinarith [hC]
        simpa [Q, ν'] using hbase.trans hscale
      _ = (others.card : ℝ) * C *
          (1 + Real.log n / δ ^ 2) := by
        simp
        ring
      _ ≤ (k : ℝ) * C * (1 + Real.log n / δ ^ 2) := by
        have hcard : (others.card : ℝ) ≤ k := by
          have hcardNat : others.card ≤ k := by
            simpa using (Finset.card_le_univ others)
          exact_mod_cast hcardNat
        have hfac : 0 ≤ C * (1 + Real.log n / δ ^ 2) := by positivity
        nlinarith
  have hkl_arm (j : Fin k) :
      klDiv (ν.P j) (ν'.P j) =
        if j = i then ENNReal.ofReal d else 0 := by
    change klDiv (gaussianReal (μvec j) 1) (gaussianReal (μ' j) 1) = _
    rw [gaussian_relative_entropy_formula (μvec j) (μ' j)
      (by norm_num)]
    by_cases hj : j = i
    · subst j
      rw [if_pos rfl]
      congr 1
      dsimp [d]
      rw [hμi, hμ'i]
      ring
    · rw [if_neg hj]
      simp [μ', hj]
  have hKLfinite (j : Fin k) :
      klDiv (ν.P j) (ν'.P j) ≠ ⊤ := by
    rw [hkl_arm]
    split
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hdiv := bandit_divergence_decomposition ν ν' hKLfinite π n
  have hDtoReal :
      (klDiv P Q).toReal = Ep * d := by
    dsimp [P, Q]
    rw [hdiv]
    simp only [hkl_arm]
    rw [show (∑ j, ENNReal.ofReal
          (∫ h, (armPullCount j h : ℝ) ∂banditMeasure ν π n) *
          (if j = i then ENNReal.ofReal d else 0)) =
        ENNReal.ofReal Ep * ENNReal.ofReal d by simp [Ep, P]]
    rw [← ENNReal.ofReal_mul hEp0]
    rw [ENNReal.toReal_ofReal]
    positivity
  have hDfinite : klDiv P Q ≠ ⊤ := by
    dsimp [P, Q]
    rw [hdiv]
    apply ENNReal.sum_ne_top.2
    intro j _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKLfinite j)
  let A : Set (BanditHistory k n) :=
    {h | (n : ℝ) / 2 < (armPullCount i h : ℝ)}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (measurable_armPullCount_lower i)
  have hBH :
      (1 / 2 : ℝ) * Real.exp (-(Ep * d)) ≤
        P.real A + Q.real Aᶜ := by
    rw [← hDtoReal]
    simpa [P, Q] using
      (bretagnolle_huber_inequality
        (banditMeasure ν π n) (banditMeasure ν' π n) hA hDfinite)
  have hPevent :
      P.real A * ((n : ℝ) / 2) ≤ Ep := by
    dsimp [Ep]
    apply integral_ge_const_mul_measureReal_lower P hA
      (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      ((n : ℝ) / 2)
      (by dsimp [P]; exact arm_pull_count_integrable_lower ν π i)
      (by positivity)
    · intro h hh
      exact hh.le
    · intro h
      positivity
  have hQevent :
      Q.real Aᶜ * ((n : ℝ) / 2) ≤ EqOthers := by
    apply integral_ge_const_mul_measureReal_lower Q hA.compl
      (fun h : BanditHistory k n ↦
        ∑ j ∈ others, (armPullCount j h : ℝ))
      ((n : ℝ) / 2)
    · exact integrable_finset_sum others fun j hj ↦ hIntQ j
    · positivity
    · intro h hh
      have hile : (armPullCount i h : ℝ) ≤ (n : ℝ) / 2 := by
        simpa [A] using hh
      have hsplit :
          (∑ j ∈ others, (armPullCount j h : ℝ)) +
              (armPullCount i h : ℝ) = n := by
        rw [← pull_count_sum_lower h]
        simpa [others] using
          (Finset.sum_erase_add
            (f := fun j ↦ (armPullCount j h : ℝ))
            (Finset.mem_univ i))
      linarith
    · intro h
      positivity
  have hPA :
      P.real A ≤
        (2 * (C * (1 + Real.log n / Δ ^ 2))) / n := by
    apply (le_div_iff₀ hnR).2
    nlinarith [hPevent, hEpUpper]
  have hQA :
      Q.real Aᶜ ≤
        (2 * ((k : ℝ) * C * (1 + Real.log n / δ ^ 2))) / n := by
    apply (le_div_iff₀ hnR).2
    nlinarith [hQevent, hEqOthers]
  have hnum :
      2 * (C * (1 + Real.log n / Δ ^ 2)) +
          2 * ((k : ℝ) * C * (1 + Real.log n / δ ^ 2)) ≤
        M * (1 + Real.log n) := by
    have hL0 : 0 ≤ Real.log (n : ℝ) := le_trans zero_le_one hlog
    have hpartΔ :
        1 + Real.log n / Δ ^ 2 ≤
          (1 + 1 / Δ ^ 2) * (1 + Real.log n) := by
      have hinv : 0 ≤ 1 / Δ ^ 2 := by positivity
      calc
        1 + Real.log n / Δ ^ 2 ≤
            (1 + Real.log n / Δ ^ 2) +
              (Real.log n + 1 / Δ ^ 2) :=
          le_add_of_nonneg_right (add_nonneg hL0 hinv)
        _ = (1 + 1 / Δ ^ 2) * (1 + Real.log n) := by ring
    have hpartδ :
        1 + Real.log n / δ ^ 2 ≤
          (1 + 1 / δ ^ 2) * (1 + Real.log n) := by
      have hinv : 0 ≤ 1 / δ ^ 2 := by positivity
      calc
        1 + Real.log n / δ ^ 2 ≤
            (1 + Real.log n / δ ^ 2) +
              (Real.log n + 1 / δ ^ 2) :=
          le_add_of_nonneg_right (add_nonneg hL0 hinv)
        _ = (1 + 1 / δ ^ 2) * (1 + Real.log n) := by ring
    have hfirst := mul_le_mul_of_nonneg_left hpartΔ (by positivity : 0 ≤ 2 * C)
    have hsecond := mul_le_mul_of_nonneg_left hpartδ
      (by positivity : 0 ≤ 2 * (k : ℝ) * C)
    convert add_le_add hfirst hsecond using 1 <;> dsimp [M] <;> ring
  have herrors :
      P.real A + Q.real Aᶜ ≤ M * (1 + Real.log n) / n := by
    calc
      P.real A + Q.real Aᶜ ≤
          (2 * (C * (1 + Real.log n / Δ ^ 2))) / n +
            (2 * ((k : ℝ) * C *
              (1 + Real.log n / δ ^ 2))) / n := add_le_add hPA hQA
      _ = (2 * (C * (1 + Real.log n / Δ ^ 2)) +
          2 * ((k : ℝ) * C *
            (1 + Real.log n / δ ^ 2))) / n := by ring
      _ ≤ M * (1 + Real.log n) / n :=
        div_le_div_of_nonneg_right hnum hnR.le
  have htest :
      (1 / 2 : ℝ) * Real.exp (-(Ep * d)) ≤
        M * (1 + Real.log n) / n :=
    hBH.trans herrors
  have hleftpos :
      0 < (1 / 2 : ℝ) * Real.exp (-(Ep * d)) := by positivity
  have hlogineq :=
    Real.log_le_log hleftpos htest
  have hOneLog : 0 < 1 + Real.log (n : ℝ) := by linarith
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
      (Real.exp_ne_zero _),
    Real.log_exp,
    Real.log_div (mul_ne_zero (ne_of_gt hM) (ne_of_gt hOneLog))
      (ne_of_gt hnR),
    Real.log_mul (ne_of_gt hM) (ne_of_gt hOneLog)] at hlogineq
  have hlogOne :
      Real.log (1 + Real.log (n : ℝ)) ≤
        Real.log 2 + Real.log (Real.log (n : ℝ)) := by
    have harg :
        1 + Real.log (n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      linarith
    calc
      Real.log (1 + Real.log (n : ℝ)) ≤
          Real.log (2 * Real.log (n : ℝ)) :=
        Real.log_le_log hOneLog harg
      _ = Real.log 2 + Real.log (Real.log (n : ℝ)) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hlogpos)]
  have hlower :
      (Real.log n - Real.log 2 - Real.log (Real.log n) - c₀) / d ≤ Ep := by
    apply (div_le_iff₀ hd).2
    dsimp [c₀]
    linarith only [hlogineq, hlogOne]
  have hratio :
      S n ≤ Ep / Real.log n := by
    dsimp [S]
    exact div_le_div_of_nonneg_right hlower hlogpos.le
  calc
    a < S n := haSn
    _ ≤ Ep / Real.log n := hratio
    _ = (∫ h, (armPullCount i h : ℝ)
          ∂banditMeasure (gaussianBandit μvec) π n) /
            Real.log n := by
      rfl
