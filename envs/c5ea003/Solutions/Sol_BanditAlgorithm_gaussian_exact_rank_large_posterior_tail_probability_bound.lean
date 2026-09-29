-- Prove2me | solution 1 for BanditAlgorithm.gaussian_exact_rank_large_posterior_tail_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T01:26:04.761902+00:00
-- url     : https://prove2.me/submissions/8e43bbc4-dd21-4ae2-9825-fd03256452bf

import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail
import Theorems.Thm_BanditAlgorithm_armStoppedCenteredSum_eq_firstRewardsMean
import Theorems.Thm_BanditAlgorithm_gaussianBandit_isSubgaussian_one
import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private noncomputable def Qsub (u : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Ioi u)

private theorem Qsub_upper (u : ℝ) (hu : 0 ≤ u) :
    Qsub u ≤ Real.exp (-u ^ 2 / 2) := by
  have hsub :
      HasSubgaussianMGF id 1 (gaussianReal 0 1) := by
    constructor
    · exact fun t ↦ integrable_exp_mul_gaussianReal t
    · intro t
      rw [mgf_id_gaussianReal]
      norm_num
  apply (MeasureTheory.measureReal_mono
    (show Set.Ioi u ⊆ {x : ℝ | u ≤ id x} by
      intro x hx
      change u < x at hx
      exact hx.le)).trans
  simpa using hsub.measure_ge_le hu

private theorem posterior_tail_standardize_sub
    (m c : ℝ) (s : ℕ) (hs : 0 < s) :
    (gaussianReal m ((s : NNReal))⁻¹).real (Set.Ioi c) =
      Qsub ((c - m) * Real.sqrt s) := by
  let r : ℝ := Real.sqrt s
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hmap1 :
      (gaussianReal m ((s : NNReal))⁻¹).map (fun x ↦ x - m) =
        gaussianReal 0 ((s : NNReal))⁻¹ := by
    simpa using
      (gaussianReal_map_sub_const
        (μ := m) (v := ((s : NNReal))⁻¹) m)
  have hvar :
      NNReal.mk (r ^ 2) (sq_nonneg r) * ((s : NNReal))⁻¹ = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_inv,
      NNReal.coe_natCast, NNReal.coe_one]
    have hrsq : r ^ 2 = s := by
      dsimp [r]
      rw [Real.sq_sqrt]
      positivity
    rw [hrsq]
    field_simp
  have hmap2 :
      (gaussianReal 0 ((s : NNReal))⁻¹).map (fun x ↦ r * x) =
        gaussianReal 0 1 := by
    simpa [hvar] using
      (gaussianReal_map_const_mul
        (μ := (0 : ℝ)) (v := ((s : NNReal))⁻¹) r)
  have hmap :
      (gaussianReal m ((s : NNReal))⁻¹).map
          (fun x ↦ r * (x - m)) =
        gaussianReal 0 1 := by
    rw [show (fun x : ℝ ↦ r * (x - m)) =
        (fun x ↦ r * x) ∘ (fun x ↦ x - m) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hmap1, hmap2]
  have happ := congrArg
    (fun P : Measure ℝ ↦ P.real (Set.Ioi ((c - m) * r))) hmap
  change
    ((gaussianReal m ((s : NNReal))⁻¹).map
      (fun x ↦ r * (x - m))).real (Set.Ioi ((c - m) * r)) =
      (gaussianReal 0 1).real (Set.Ioi ((c - m) * r)) at happ
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Ioi] at happ
  have hpre :
      (fun x : ℝ ↦ r * (x - m)) ⁻¹' Set.Ioi ((c - m) * r) =
        Set.Ioi c := by
    ext x
    change (c - m) * r < r * (x - m) ↔ c < x
    constructor <;> intro h <;> nlinarith
  simpa [Qsub, r, hpre] using happ

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      ∀ (i₀ : Fin k),
        banditArmMean (gaussianBandit μvec) i₀ =
          banditOptimalMean (gaussianBandit μvec) →
      ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
      ∀ n : ℕ, 2 ≤ n →
      ∀ s : ℕ, 0 < s →
        (banditMeasure (gaussianBandit μvec) π n).real
          {h : BanditHistory k n |
            s < armPullCount i h ∧
              1 / (n : ℝ) <
                gaussianTSTailProb i s
                  (banditArmMean (gaussianBandit μvec) i₀ -
                    banditGap (gaussianBandit μvec) i / 2) h} ≤
          if 2 * Real.log n /
                (banditGap (gaussianBandit μvec) i / 2) ^ 2 < (s : ℝ)
          then
            Real.exp
              (-((s : ℝ) *
                (banditGap (gaussianBandit μvec) i / 2 -
                  Real.sqrt (2 * Real.log n / s))) ^ 2 /
                ((2 : ℝ) * (s : ℝ) * 1))
          else 1 := by
  intro k _ μvec π i₀ hi₀ i hgap n hn s hs
  let ν := gaussianBandit μvec
  let Δ : ℝ := banditGap ν i
  let e : ℝ := Δ / 2
  let A : ℝ := Real.log n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 < A := by
    dsimp [A]
    exact Real.log_pos (by exact_mod_cast hn)
  have he : 0 < e := by dsimp [e, Δ, ν]; positivity
  change
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          s < armPullCount i h ∧
            1 / (n : ℝ) <
              gaussianTSTailProb i s
                (banditArmMean ν i₀ - Δ / 2) h} ≤
      if 2 * A / e ^ 2 < (s : ℝ) then
        Real.exp
          (-((s : ℝ) *
            (e - Real.sqrt (2 * A / s))) ^ 2 /
            ((2 : ℝ) * (s : ℝ) * 1))
      else 1
  by_cases hcut : 2 * A / e ^ 2 < (s : ℝ)
  · rw [if_pos hcut]
    let d : ℝ := e - Real.sqrt (2 * A / s)
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hd : 0 ≤ d := by
      have hsqrt :
          Real.sqrt (2 * A / s) < e := by
        apply (Real.sqrt_lt' he).2
        rw [div_lt_iff₀ hsR]
        have he2 : 0 < e ^ 2 := sq_pos_of_pos he
        rw [div_lt_iff₀ he2] at hcut
        nlinarith
      dsimp [d]
      linarith
    have htail :=
      (bandit_adaptive_stopped_centered_sum_tail
        ν (gaussianBandit_isSubgaussian_one μvec)
        i s (π := π) (n := n) hd).1
    calc
      (banditMeasure ν π n).real
          {h : BanditHistory k n |
            s < armPullCount i h ∧
              1 / (n : ℝ) <
                gaussianTSTailProb i s
                  (banditArmMean ν i₀ - Δ / 2) h} ≤
          (banditMeasure ν π n).real
            {h : BanditHistory k n |
              (s : ℝ) * d ≤
                armStoppedCenteredSum ν i s n h} := by
        refine MeasureTheory.measureReal_mono ?_ (by simp)
        intro h hh
        have hcount : s ≤ armPullCount i h :=
          Nat.le_of_lt hh.1
        have hmean :=
          armStoppedCenteredSum_eq_firstRewardsMean
            ν i s h hs hcount
        have hμi : banditArmMean ν i =
            banditOptimalMean ν - Δ := by
          dsimp [Δ]
          unfold banditGap
          ring
        have hc :
            banditArmMean ν i₀ - Δ / 2 =
              banditArmMean ν i + e := by
          dsimp [e]
          rw [hi₀, hμi]
          ring
        have hpost :
            Qsub (((banditArmMean ν i + e) -
                armFirstRewardsMean i s h) * Real.sqrt s) >
              1 / (n : ℝ) := by
          have hsne : s ≠ 0 := Nat.ne_of_gt hs
          have hh2 := hh.2
          unfold gaussianTSTailProb at hh2
          rw [if_neg hsne, hc] at hh2
          change 1 / (n : ℝ) <
            (gaussianReal (armFirstRewardsMean i s h)
                ((s : NNReal))⁻¹).real
              (Set.Ioi (banditArmMean ν i + e)) at hh2
          rw [posterior_tail_standardize_sub
            (armFirstRewardsMean i s h)
            (banditArmMean ν i + e) s hs] at hh2
          exact hh2
        have hdev :
            d < armFirstRewardsMean i s h - banditArmMean ν i := by
          by_contra hnot
          have hle :
              armFirstRewardsMean i s h - banditArmMean ν i ≤ d :=
            le_of_not_gt hnot
          have hu :
              Real.sqrt (2 * A) ≤
                ((banditArmMean ν i + e) -
                  armFirstRewardsMean i s h) * Real.sqrt s := by
            have hsqrtmul :
                Real.sqrt (2 * A / s) * Real.sqrt s =
                  Real.sqrt (2 * A) := by
              rw [Real.sqrt_div (by positivity : 0 ≤ 2 * A) s]
              field_simp
            dsimp [d] at hle
            have hbase :
                Real.sqrt (2 * A / s) ≤
                  (banditArmMean ν i + e) -
                    armFirstRewardsMean i s h := by
              linarith
            have hmul := mul_le_mul_of_nonneg_right hbase
              (Real.sqrt_nonneg (s : ℝ))
            rw [hsqrtmul] at hmul
            exact hmul
          have hu0 : 0 ≤
              ((banditArmMean ν i + e) -
                armFirstRewardsMean i s h) * Real.sqrt s :=
            (Real.sqrt_nonneg (2 * A)).trans hu
          have hQ := Qsub_upper
            (((banditArmMean ν i + e) -
              armFirstRewardsMean i s h) * Real.sqrt s) hu0
          have hsq :
              2 * A ≤
                (((banditArmMean ν i + e) -
                  armFirstRewardsMean i s h) * Real.sqrt s) ^ 2 := by
            have hsqmono :
                (Real.sqrt (2 * A)) ^ 2 ≤
                  (((banditArmMean ν i + e) -
                    armFirstRewardsMean i s h) * Real.sqrt s) ^ 2 :=
              (sq_le_sq₀ (Real.sqrt_nonneg (2 * A)) hu0).2 hu
            rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * A)] at hsqmono
            exact hsqmono
          have hexp :
              Real.exp
                  (-(((banditArmMean ν i + e) -
                    armFirstRewardsMean i s h) * Real.sqrt s) ^ 2 / 2) ≤
                1 / (n : ℝ) := by
            calc
              _ ≤ Real.exp (-A) := by
                apply Real.exp_le_exp.mpr
                nlinarith
              _ = 1 / (n : ℝ) := by
                dsimp [A]
                rw [Real.exp_neg, Real.exp_log hn0]
                simp [one_div]
          linarith
        change (s : ℝ) * d ≤ armStoppedCenteredSum ν i s n h
        rw [hmean]
        nlinarith [hsR]
      _ ≤ Real.exp (-((s : ℝ) * d ^ 2) / 2) := by
        convert htail using 1 <;> ring
      _ = Real.exp
          (-((s : ℝ) *
            (e - Real.sqrt (2 * A / s))) ^ 2 /
            ((2 : ℝ) * (s : ℝ) * 1)) := by
        congr 1
        dsimp [d]
        field_simp
  · rw [if_neg hcut]
    have hmono :
        (banditMeasure ν π n).real
          {h : BanditHistory k n |
            s < armPullCount i h ∧
              1 / (n : ℝ) <
                gaussianTSTailProb i s
                  (banditArmMean ν i₀ - Δ / 2) h} ≤
          (banditMeasure ν π n).real Set.univ :=
      MeasureTheory.measureReal_mono (Set.subset_univ _)
    simpa using hmono
