-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_suboptimal_exact_rank_overshoot_sum_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T01:41:32.76528+00:00
-- url     : https://prove2.me/submissions/4a528355-8783-420e-abf7-8aa1d6310f24

import Theorems.Thm_BanditAlgorithm_gaussian_exact_rank_posterior_overshoot_probability_bound
import Theorems.Thm_BanditAlgorithm_bandit_ucb_index_exponential_sum_bound_sharp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem measurable_gaussianReal_real_Ioi_sub (c : ℝ) :
    Measurable (fun p : ℝ × NNReal ↦
      (gaussianReal p.1 p.2).real (Set.Ioi c)) := by
  have hpdf :
      Measurable
        (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) := by
    rw [show
      (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) =
        fun p ↦ ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi * (p.1.2 : ℝ)))⁻¹ *
            Real.exp (-((p.2 - p.1.1) ^ 2) / (2 * (p.1.2 : ℝ)))) by
      funext p
      rfl]
    fun_prop
  have hint :
      Measurable
        (fun p : ℝ × NNReal ↦
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal) := by
    apply Measurable.ennreal_toReal
    have hrestricted :
        Measurable
          (fun z : (ℝ × NNReal) × ℝ ↦
            (Set.Ioi c).indicator
              (fun x ↦ gaussianPDF z.1.1 z.1.2 x) z.2) :=
      hpdf.indicator
        (measurableSet_Ioi.preimage measurable_snd)
    simpa only [lintegral_indicator measurableSet_Ioi] using
      (hrestricted.lintegral_prod_right' (ν := (volume : Measure ℝ)))
  have hzero :
      Measurable
        (fun p : ℝ × NNReal ↦ if c < p.1 then (1 : ℝ) else 0) :=
    Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      measurable_const measurable_const
  have heq :
      (fun p : ℝ × NNReal ↦ (gaussianReal p.1 p.2).real (Set.Ioi c)) =
        fun p ↦ if p.2 = 0 then
          (if c < p.1 then 1 else 0)
        else
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal := by
    funext p
    by_cases hp : p.2 = 0
    · rw [if_pos hp, hp, gaussianReal_zero_var]
      by_cases hc : c < p.1 <;> simp [Measure.real, Set.indicator, hc]
    · rw [if_neg hp, Measure.real, gaussianReal_apply p.1 hp]
  rw [heq]
  exact Measurable.ite
    ((measurableSet_singleton (0 : NNReal)).preimage measurable_snd)
    hzero hint

private theorem armPullCount_eq_sum_indicator_sub {k m : ℕ}
    (i : Fin k) (h : BanditHistory k m) :
    armPullCount i h =
      ∑ t : Fin m, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset :
      {t | (h t).1 = i}.toFinset =
        Finset.univ.filter fun t ↦ (h t).1 = i := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℕ) (fun t : Fin m ↦ (h t).1 = i)
      Finset.univ).symm

private theorem measurable_armPullCount_sub {k m : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ armPullCount i h) := by
  simp_rw [armPullCount_eq_sum_indicator_sub]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem measurable_armPullCountBefore_sub {k n : ℕ}
    (i : Fin k) (t : Fin n) :
    Measurable (fun h : BanditHistory k n ↦ armPullCountBefore i t h) := by
  simp_rw [show ∀ h : BanditHistory k n,
      armPullCountBefore i t h =
        ∑ u : Fin n, if u < t ∧ (h u).1 = i then 1 else 0 by
    intro h
    unfold armPullCountBefore
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]]
  apply Finset.measurable_sum
  intro u hu
  apply Measurable.ite
  · change MeasurableSet
      {h : BanditHistory k n | u < t ∧ (h u).1 = i}
    by_cases hut : u < t
    · have heq :
          {h : BanditHistory k n | u < t ∧ (h u).1 = i} =
            (fun h : BanditHistory k n ↦ (h u).1) ⁻¹' {i} := by
          ext h
          simp [hut]
      rw [heq]
      exact (measurableSet_singleton i).preimage
        (measurable_fst.comp
          (measurable_pi_apply u :
            Measurable (fun h : BanditHistory k n ↦ h u)))
    · simp [hut]
  · exact measurable_const
  · exact measurable_const

private theorem measurable_armFirstRewardsMean_sub {k n : ℕ}
    (i : Fin k) (s : ℕ) :
    Measurable (fun h : BanditHistory k n ↦ armFirstRewardsMean i s h) := by
  rw [show
    (fun h : BanditHistory k n ↦ armFirstRewardsMean i s h) =
      fun h ↦
        (∑ t : Fin n,
          if (h t).1 = i ∧ armPullCountBefore i t h < s
          then (h t).2 else 0) / s by
    funext h
    unfold armFirstRewardsMean
    simp [Finset.sum_filter]]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro t ht
  apply Measurable.ite
  · exact MeasurableSet.inter
      ((measurableSet_singleton i).preimage
        (measurable_fst.comp (measurable_pi_apply t)))
      (measurableSet_lt
        (measurable_armPullCountBefore_sub i t) measurable_const)
  · exact measurable_snd.comp (measurable_pi_apply t)
  · exact measurable_const

private theorem measurable_gaussianTSTailProb_sub {k n : ℕ}
    (i : Fin k) (s : ℕ) (c : ℝ) :
    Measurable (fun h : BanditHistory k n ↦ gaussianTSTailProb i s c h) := by
  unfold gaussianTSTailProb
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, if_false]
    have hp : Measurable
        (fun h : BanditHistory k n ↦
          (armFirstRewardsMean i s h, ((s : NNReal))⁻¹)) :=
      (measurable_armFirstRewardsMean_sub i s).prodMk measurable_const
    simpa only [Function.comp_apply] using
      (measurable_gaussianReal_real_Ioi_sub c).comp hp

private theorem armPullCount_le_horizon_sub {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    armPullCount i h ≤ n := by
  rw [armPullCount]
  simpa using Finset.card_le_univ ({t | (h t).1 = i}.toFinset)

private theorem sum_realized_ranks_eq_sub {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) (f : ℕ → ENNReal) :
    (∑ s ∈ Finset.range (armPullCount i h), f s) =
      ∑ s ∈ Finset.range n,
        if s < armPullCount i h then f s else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro s hs
    have hslt : s < armPullCount i h := Finset.mem_range.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr
        (hslt.trans_le (armPullCount_le_horizon_sub i h)), hslt⟩
  · intro s hsn hsnot
    exact (hsnot (Finset.mem_range.mpr (Finset.mem_filter.mp hsn).2)).elim

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i₀ : Fin k),
          banditArmMean (gaussianBandit μvec) i₀ =
            banditOptimalMean (gaussianBandit μvec) →
        ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
        ∀ ε : ℝ, 0 < ε →
          ε < banditGap (gaussianBandit μvec) i →
        ∀ n : ℕ, 2 ≤ n →
          (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
              (if 1 / (n : ℝ) <
                  gaussianTSTailProb i s
                    (banditArmMean (gaussianBandit μvec) i₀ -
                      ε) h
                then (1 : ℝ≥0∞) else 0)
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal
              (1 + 2 / (banditGap (gaussianBandit μvec) i - ε) ^ 2 *
                (Real.log n + Real.sqrt (Real.pi * Real.log n) + 1)) := by
  intro k _ μvec π i₀ hi₀ i hgap ε hε hεgap n hn
  let ν := gaussianBandit μvec
  let Δ : ℝ := banditGap ν i
  let e : ℝ := Δ - ε
  let A : ℝ := Real.log n
  let c : ℝ := banditArmMean ν i₀ - ε
  let w : ℕ → ℝ := fun s ↦
    if 2 * A / e ^ 2 < (s : ℝ) then
      Real.exp
        (-((s : ℝ) * (e - Real.sqrt (2 * A / s))) ^ 2 /
          ((2 : ℝ) * (s : ℝ) * 1))
    else 1
  let f : ℕ → BanditHistory k n → ENNReal := fun s h ↦
    if s < armPullCount i h ∧
        1 / (n : ℝ) < gaussianTSTailProb i s c h
    then 1 else 0
  have he : 0 < e := by dsimp [e, Δ, ν]; linarith
  have hA : 0 < A := by
    dsimp [A]
    exact Real.log_pos (by exact_mod_cast hn)
  have hw (s : ℕ) : 0 ≤ w s := by
    dsimp [w]
    split <;> positivity
  have hf (s : ℕ) : Measurable (f s) := by
    apply Measurable.ite
    · exact MeasurableSet.inter
        (measurableSet_lt measurable_const (measurable_armPullCount_sub i))
        (measurableSet_lt measurable_const
          (measurable_gaussianTSTailProb_sub i s c))
    · exact measurable_const
    · exact measurable_const
  have hrewrite :
      (fun h : BanditHistory k n ↦
        ∑ s ∈ Finset.range (armPullCount i h),
          (if 1 / (n : ℝ) < gaussianTSTailProb i s c h
            then (1 : ENNReal) else 0)) =
        fun h ↦ ∑ s ∈ Finset.range n, f s h := by
    funext h
    rw [sum_realized_ranks_eq_sub]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hcount : s < armPullCount i h
    · simp [f, hcount]
    · simp [f, hcount]
  change
    (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
        (if 1 / (n : ℝ) < gaussianTSTailProb i s c h
          then (1 : ENNReal) else 0) ∂banditMeasure ν π n) ≤
      ENNReal.ofReal
        (1 + 2 / e ^ 2 * (A + Real.sqrt (Real.pi * A) + 1))
  rw [hrewrite, MeasureTheory.lintegral_finsetSum (Finset.range n)
    (fun s hs ↦ hf s)]
  have hterms :
      (∑ s ∈ Finset.range n,
          ∫⁻ h, f s h ∂banditMeasure ν π n) ≤
        ∑ s ∈ Finset.range n, ENNReal.ofReal (w s) := by
    apply Finset.sum_le_sum
    intro s hsrange
    by_cases hs0 : s = 0
    · subst s
      calc
        (∫⁻ h, f 0 h ∂banditMeasure ν π n) ≤
            ∫⁻ _h, (1 : ENNReal) ∂banditMeasure ν π n := by
          apply lintegral_mono
          intro h
          dsimp [f]
          split <;> simp
        _ = 1 := by simp
        _ = ENNReal.ofReal (w 0) := by
          simp [w]
    · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
      let E : Set (BanditHistory k n) :=
        {h | s < armPullCount i h ∧
          1 / (n : ℝ) < gaussianTSTailProb i s c h}
      have hE : MeasurableSet E := by
        exact MeasurableSet.inter
          (measurableSet_lt measurable_const (measurable_armPullCount_sub i))
          (measurableSet_lt measurable_const
            (measurable_gaussianTSTailProb_sub i s c))
      have hlin :
          (∫⁻ h, f s h ∂banditMeasure ν π n) =
            (banditMeasure ν π n) E := by
        rw [show f s = E.indicator (fun _ ↦ (1 : ENNReal)) by
          funext h
          dsimp [f, E]
          by_cases hh : s < armPullCount i h ∧
              1 / (n : ℝ) < gaussianTSTailProb i s c h
          · simp [Set.indicator, hh]
          · simp [Set.indicator, hh]]
        exact lintegral_indicator_one hE
      rw [hlin, ← ofReal_measureReal (by simp)]
      apply ENNReal.ofReal_le_ofReal
      simpa [E, c, w, ν, Δ, e, A] using
        (gaussian_exact_rank_posterior_overshoot_probability_bound
          k μvec π i₀ hi₀ i hgap ε hε hεgap n hn s hspos)
  apply hterms.trans
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    have hsharp :=
      bandit_ucb_index_exponential_sum_bound_sharp
        (n := n) (ε := e) (a := A) he hA
    have hrange :
        (∑ s ∈ Finset.range n, w s) ≤
          1 + ∑ s ∈ Finset.Icc 1 n, w s := by
      have hsplit :
          (∑ s ∈ Finset.range n, w s) =
            w 0 + ∑ s ∈ Finset.Icc 1 (n - 1), w s := by
        have hset :
            Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
          ext s
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hset, Finset.sum_insert (by simp)]
      rw [hsplit]
      have hsub : Finset.Icc 1 (n - 1) ⊆ Finset.Icc 1 n := by
        intro s hs
        simp only [Finset.mem_Icc] at hs ⊢
        omega
      have hsumsub :
          (∑ s ∈ Finset.Icc 1 (n - 1), w s) ≤
            ∑ s ∈ Finset.Icc 1 n, w s :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun s hs hnot ↦ hw s)
      have hw0 : w 0 = 1 := by simp [w]
      rw [hw0]
      gcongr
    have hsharpw :
        (∑ s ∈ Finset.Icc 1 n, w s) ≤
          2 / e ^ 2 * (A + Real.sqrt (Real.pi * A) + 1) := by
      simpa [w] using hsharp
    calc
      (∑ s ∈ Finset.range n, w s) ≤
          1 + ∑ s ∈ Finset.Icc 1 n, w s := hrange
      _ ≤ 1 + 2 / e ^ 2 *
          (A + Real.sqrt (Real.pi * A) + 1) := by gcongr
      _ = 1 + 2 / e ^ 2 *
          (A + Real.sqrt (Real.pi * A) + 1) := rfl
  · intro s hs
    exact hw s
