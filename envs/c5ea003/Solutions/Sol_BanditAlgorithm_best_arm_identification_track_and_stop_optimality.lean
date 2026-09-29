-- Prove2me | solution 1 for BanditAlgorithm.best_arm_identification_track_and_stop_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T18:10:06.375982+00:00
-- url     : https://prove2.me/submissions/9a32c611-eabf-4199-b638-bc35bdd2bbcd

import Theorems.Thm_BanditAlgorithm_best_arm_identification_sample_complexity_lower_bound
import Theorems.Thm_BanditAlgorithm_best_arm_identification_track_and_stop_upper_bound

/-!
# Track-and-Stop asymptotic optimality (L&S Theorem 33.6) — the squeeze

The two halves of Theorem 33.6 are already available:

* the **lower** half is Theorem 33.5,
  `BanditAlgorithm.best_arm_identification_sample_complexity_lower_bound`:
  every sound learner satisfies `c*(ν) · log(1/(4δ)) ≤ E_{νπ}[τ_δ]`;
* the **upper** half is
  `BanditAlgorithm.best_arm_identification_track_and_stop_upper_bound`
  (= Garivier–Kaufmann, COLT 2016, Theorem 14 at `α = 1`, together with their
  Proposition 13 for the finiteness of `E[τ_δ]`): Track-and-Stop is sound at
  every `δ` and its normalised sample complexity is asymptotically at most
  `c*(ν)`.

This file performs the remaining work: the squeeze.  Since
`log(1/(4δ)) = log(1/δ) − log 4`, the lower half gives

  `E[τ_δ].toReal / log(1/δ) ≥ c*(ν).toReal · (1 − log 4 / log(1/δ))`,

whose right-hand side tends to `c*(ν).toReal` as `δ → 0⁺`; combined with the
upper half this pins the limit.  Along the way `c*(ν) ≠ ⊤` has to be derived:
if it were `⊤`, then already at `δ = 1/8` the lower half would force
`E[τ_δ] = ⊤`, contradicting the finiteness supplied by the upper half.
-/

open MeasureTheory ProbabilityTheory Filter ENNReal

namespace BanditAlgorithm

theorem _root_.solution {k : ℕ} (hk : 0 < k) :
    ∃ (π : BanditPolicy k) (τ : ℝ → (ℕ → Fin k × ℝ) → ℕ∞)
      (ψ : ℝ → (ℕ → Fin k × ℝ) → Fin k),
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∃ hτ : IsBanditStoppingTime (τ δ),
          Measurable[hτ.measurableSpace] (ψ δ) ∧
            IsSoundBAI δ π (τ δ) (ψ δ) (Set.range (gaussianBandit (k := k)))) ∧
      ∀ ν ∈ Set.range (gaussianBandit (k := k)), (∃! i, i ∈ banditOptimalArms ν) →
        Tendsto
          (fun δ : ℝ ↦
            (∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π).toReal / Real.log (1 / δ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (baiComplexity ν (Set.range (gaussianBandit (k := k)))).toReal) := by
  obtain ⟨π, τ, ψ, hsound, hupper⟩ :=
    best_arm_identification_track_and_stop_upper_bound (k := k) hk
  refine ⟨π, τ, ψ, hsound, ?_⟩
  intro ν hν huniq
  obtain ⟨hfin, hlim⟩ := hupper ν hν huniq
  set 𝓔 : Set (StochasticBandit k) := Set.range (gaussianBandit (k := k)) with h𝓔
  set c : ℝ≥0∞ := baiComplexity ν 𝓔 with hc
  set I : ℝ → ℝ≥0∞ := fun δ ↦ ∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π with hIdef
  -- The lower half, Theorem 33.5, applied to the learner supplied by the upper half.
  have hlow : ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      c * ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤ I δ := by
    intro δ hδ
    obtain ⟨hτ, hψ, hs⟩ := hsound δ hδ
    exact best_arm_identification_sample_complexity_lower_bound 𝓔 δ hδ π (τ δ) (ψ δ) hτ hψ hs ν hν
  -- Step 1: the characteristic time is finite.
  have hc_ne : c ≠ ⊤ := by
    intro htop
    have h8 : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    have h := hlow (1 / 8) h8
    have hlog : (1 : ℝ) / (4 * (1 / 8)) = 2 := by norm_num
    rw [htop, hlog] at h
    have hne : ENNReal.ofReal (Real.log 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.log_pos (by norm_num)
    rw [ENNReal.top_mul hne] at h
    exact hfin (1 / 8) h8 (top_le_iff.mp h)
  -- Step 2: the real-valued form of the lower bound, for `δ < 1/4`.
  have key : ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
      c.toReal * (Real.log (1 / δ) - Real.log 4) ≤ (I δ).toReal := by
    intro δ hδ0 hδ4
    have hδ : δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hδ0, by linarith⟩
    have h4δ : (0 : ℝ) < 4 * δ := by linarith
    have hL : 0 ≤ Real.log (1 / (4 * δ)) :=
      Real.log_nonneg ((one_le_div h4δ).mpr (by linarith))
    have h := ENNReal.toReal_mono (hfin δ hδ) (hlow δ hδ)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at h
    have hsplit : Real.log (1 / (4 * δ)) = Real.log (1 / δ) - Real.log 4 := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hδ0)]
      ring
    rwa [hsplit] at h
  -- Step 3: the comparison function tends to `c*(ν)`.
  have hlogtop : Tendsto (fun δ : ℝ ↦ Real.log (1 / δ)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have : Tendsto (fun δ : ℝ ↦ -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    refine this.congr fun δ ↦ ?_
    rw [one_div, Real.log_inv]
  have hg : Tendsto (fun δ : ℝ ↦ c.toReal * (1 - Real.log 4 / Real.log (1 / δ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c.toReal * (1 - 0))) := by
    refine tendsto_const_nhds.mul (tendsto_const_nhds.sub ?_)
    exact Tendsto.div_atTop tendsto_const_nhds hlogtop
  simp only [sub_zero, mul_one] at hg
  -- Step 4: the squeeze.
  rw [tendsto_order]
  constructor
  · -- lower: for every `b < c*(ν)`, eventually the ratio exceeds `b`
    intro b hb
    have h1 : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        b < c.toReal * (1 - Real.log 4 / Real.log (1 / δ)) := hg.eventually_const_lt hb
    have h2 : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
      Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [h1, h2] with δ hδ1 hδ2
    obtain ⟨hδ0, hδ4⟩ := hδ2
    have hlogpos : 0 < Real.log (1 / δ) := by
      rw [one_div]
      exact Real.log_inv δ ▸ neg_pos.mpr (Real.log_neg hδ0 (by linarith))
    calc b < c.toReal * (1 - Real.log 4 / Real.log (1 / δ)) := hδ1
      _ = c.toReal * (Real.log (1 / δ) - Real.log 4) / Real.log (1 / δ) := by
          field_simp
      _ ≤ (I δ).toReal / Real.log (1 / δ) := by
          exact div_le_div_of_nonneg_right (key δ hδ0 hδ4) hlogpos.le
  · -- upper: for every `b > c*(ν)`, eventually the ratio is below `b`
    intro b hb
    have hε : 0 < (b - c.toReal) / 2 := by linarith
    filter_upwards [hlim _ hε] with δ hδ
    calc (I δ).toReal / Real.log (1 / δ) ≤ c.toReal + (b - c.toReal) / 2 := hδ
      _ < b := by linarith

end BanditAlgorithm
