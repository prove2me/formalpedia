-- Prove2me | solution 1 for BanditAlgorithm.chernoff_stopping_time_sample_complexity_of_settling
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T14:30:07.715528+00:00
-- url     : https://prove2.me/submissions/4b4e12df-4f5f-49e7-a1ad-5da6f914c882

import Theorems.Thm_BanditAlgorithm_chernoff_stopping_time_le_integrable_plus_linear_of_settling_time

/-!
# The sample-complexity half of Theorem 33.6, from an integrable settling time

Theorem 14 delivers, for each `ε > 0`, a `δ`-free integrable time `W_ε` with

  `τ_δ ≤ W_ε + ⌈(1 + ε) c*(ν) log(1/δ)⌉`   almost surely, for every `δ ∈ (0,1)`.

Turning that family of pointwise bounds into the statement Theorem 33.6 needs is
bookkeeping in two steps:

* **finiteness.**  A single `ε` and a single `δ` already dominate `τ_δ` by an
  integrable function, so `E[τ_δ] < ∞` at every confidence level.
* **the limsup.**  Once `ε` is fixed, `E[W_ε]` is a constant, so it is divided
  away by `log(1/δ) → ∞`; the multiplicative `(1 + ε)c*` is not, which is why
  Theorem 14 has to be sharp in the multiplicative constant and may be
  arbitrarily lossy in the additive one.  Choosing `ε₀ = ε/(2(c+1))` makes
  `(1 + ε₀)c ≤ c + ε/2`, and the additive part is swallowed by the other `ε/2`.

## The degenerate arm count

Theorem 14 needs a second arm.  With `k = 1` there is nothing to test against:
`Z_t` is an infimum over the empty set, hence `⊤`, so Chernoff's rule stops at
round `0` and `τ_δ = 0` identically.  Both clauses are then trivial.  That case
is discharged here rather than pushed onto the caller, so the statement is
available for every `k` with `0 < k` — which is what the assembly of Theorem 33.6
quantifies over.

Garivier & Kaufmann, *Optimal best-arm identification strategies for one-parameter
exponential families*, COLT 2016, Theorem 14; Lattimore & Szepesvári, *Bandit
Algorithms*, Theorem 33.6.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-- `E[τ] ≤ E[W] + N` from the pointwise bound `τ ≤ W + N`. -/
theorem lintegral_le_of_le_add_const' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {τ : Ω → ℕ∞} {W : Ω → ℕ} {N : ℕ}
    (h : ∀ᵐ ω ∂μ, τ ω ≤ ((W ω : ℕ∞) + (N : ℕ∞))) [IsProbabilityMeasure μ] :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ (∫⁻ ω, (W ω : ℝ≥0∞) ∂μ) + (N : ℝ≥0∞) := by
  have hmono : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ
      ≤ ∫⁻ ω, ((W ω : ℝ≥0∞) + (N : ℝ≥0∞)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [h] with ω hω
    calc ((τ ω : ℕ∞) : ℝ≥0∞) ≤ (((W ω : ℕ∞) + (N : ℕ∞) : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_mono hω
      _ = (W ω : ℝ≥0∞) + (N : ℝ≥0∞) := by
          push_cast
          ring
  refine hmono.trans (le_of_eq ?_)
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- With a single arm the generalised-likelihood-ratio statistic is an infimum
over the empty set, hence `⊤`. -/
theorem trajGLR_eq_top_of_subsingleton (hk1 : ∀ i j : Fin k, i = j)
    (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR (k := k) t ω = ⊤ := by
  classical
  unfold trajGLR
  have hempty : {j : Fin k | j ≠ trajEmpiricalBestArm t ω} = (∅ : Set (Fin k)) := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hk1 j _
  rw [hempty]
  simp

/-- With a single arm Chernoff's rule stops at round `0`. -/
theorem chernoffStoppingTime_eq_zero_of_subsingleton (hk1 : ∀ i j : Fin k, i = j)
    (δ : ℝ) (ω : ℕ → Fin k × ℝ) :
    chernoffStoppingTime (k := k) δ ω = 0 := by
  classical
  have htop : trajGLR (k := k) 0 ω = ⊤ := trajGLR_eq_top_of_subsingleton hk1 0 ω
  have hmem : (0 : ℕ∞) ∈ {t : ℕ∞ | ∃ n : ℕ, (n : ℕ∞) = t ∧
      ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω} := by
    refine ⟨0, by simp, ?_⟩
    rw [htop]
    exact le_top
  exact le_antisymm (sInf_le hmem) bot_le

end BanditAlgorithm

open BanditAlgorithm

theorem solution {k : ℕ} [NeZero k]
    (pol : BanditAlgorithm.BanditPolicy k) (μvec : Fin k → ℝ) {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (α : Fin k → NNReal) (hαpos : ∀ i, 0 < α i)
    (hopt : BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
      (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α)
    (hsettle : ∀ ξ : ℝ, 0 < ξ →
          (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
            ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
              ∂(BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤) :
    (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∫⁻ ω, (BanditAlgorithm.chernoffStoppingTime (k := k) δ ω : ℝ≥0∞)
          ∂BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol ≠ ⊤) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (∫⁻ ω, (BanditAlgorithm.chernoffStoppingTime (k := k) δ ω : ℝ≥0∞)
              ∂BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol).toReal / Real.log (1 / δ)
            ≤ (BanditAlgorithm.baiComplexity (BanditAlgorithm.gaussianBandit μvec)
                (Set.range (BanditAlgorithm.gaussianBandit (k := k)))).toReal + ε := by
  classical
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure (gaussianBandit μvec) pol with hP
  by_cases hk2 : ∃ j : Fin k, j ≠ istar
  swap
  · -- `k = 1`: the stopping time is identically `0`
    have hk1 : ∀ i j : Fin k, i = j := by
      push_neg at hk2
      intro i j
      rw [hk2 i, hk2 j]
    have hzero : ∀ δ : ℝ, ∫⁻ ω, (chernoffStoppingTime (k := k) δ ω : ℝ≥0∞) ∂P = 0 := by
      intro δ
      have hpt : ∀ ω, (chernoffStoppingTime (k := k) δ ω : ℝ≥0∞) = 0 := by
        intro ω
        rw [chernoffStoppingTime_eq_zero_of_subsingleton hk1]
        simp
      simp [hpt]
    refine ⟨fun δ _ ↦ by rw [hzero δ]; exact zero_ne_top, ?_⟩
    intro ε hε
    filter_upwards with δ
    rw [hzero δ]
    have hnn : (0 : ℝ) ≤ (baiComplexity (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k)))).toReal := ENNReal.toReal_nonneg
    rw [ENNReal.toReal_zero, zero_div]
    linarith
  -- the genuine case
  set c : ℝ := (baiComplexity (gaussianBandit μvec)
    (Set.range (gaussianBandit (k := k)))).toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  -- the abbreviated pointwise bound
  have key : ∀ ε : ℝ, 0 < ε → ∃ W : (ℕ → Fin k × ℝ) → ℕ,
      (∫⁻ ω, (W ω : ℝ≥0∞) ∂P) ≠ ⊤ ∧ ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∫⁻ ω, (chernoffStoppingTime (k := k) δ ω : ℝ≥0∞) ∂P
          ≤ (∫⁻ ω, (W ω : ℝ≥0∞) ∂P) + ((⌈(1 + ε) * c * Real.log (1 / δ)⌉₊ : ℕ) : ℝ≥0∞) := by
    intro ε hε
    obtain ⟨W, hWint, hW⟩ :=
      chernoff_stopping_time_le_integrable_plus_linear_of_settling_time pol μvec hstar
        hk2 α hαpos hopt hsettle hε
    exact ⟨W, hWint, fun δ hδ ↦ lintegral_le_of_le_add_const' (hW δ hδ)⟩
  refine ⟨?_, ?_⟩
  · -- finiteness
    intro δ hδ
    obtain ⟨W, hWint, hbound⟩ := key 1 one_pos
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hWint, ENNReal.natCast_ne_top _⟩)
      (hbound δ hδ)
  · -- the asymptotic bound
    intro ε hε
    set ε₀ : ℝ := ε / (2 * (c + 1)) with hε₀def
    have hε₀ : 0 < ε₀ := by rw [hε₀def]; positivity
    have hinfl : (1 + ε₀) * c ≤ c + ε / 2 := by
      have h1 : ε₀ * c ≤ ε / 2 := by
        rw [hε₀def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    obtain ⟨W, hWint, hbound⟩ := key ε₀ hε₀
    set EW : ℝ := (∫⁻ ω, (W ω : ℝ≥0∞) ∂P).toReal with hEW
    have hEW0 : 0 ≤ EW := ENNReal.toReal_nonneg
    have hLtop : Tendsto (fun δ : ℝ ↦ Real.log (1 / δ)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
      have h : Tendsto (fun δ : ℝ ↦ -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      refine h.congr fun δ ↦ ?_
      rw [one_div, Real.log_inv]
    have hbig : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (EW + 1) / (ε / 2) ≤ Real.log (1 / δ) := hLtop.eventually_ge_atTop _
    have hLpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), (0 : ℝ) < Real.log (1 / δ) :=
      hLtop.eventually (eventually_gt_atTop 0)
    have hδsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT one_pos
    filter_upwards [hbig, hLpos, hδsmall] with δ hbg hL hδ
    set L : ℝ := Real.log (1 / δ) with hLdef
    have hfin : ∫⁻ ω, (chernoffStoppingTime (k := k) δ ω : ℝ≥0∞) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hWint, ENNReal.natCast_ne_top _⟩)
        (hbound δ hδ)
    have hreal : (∫⁻ ω, (chernoffStoppingTime (k := k) δ ω : ℝ≥0∞) ∂P).toReal
        ≤ EW + (⌈(1 + ε₀) * c * L⌉₊ : ℝ) := by
      have h := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hWint, ENNReal.natCast_ne_top _⟩) (hbound δ hδ)
      rwa [ENNReal.toReal_add hWint (ENNReal.natCast_ne_top _),
        ENNReal.toReal_natCast] at h
    have hceil : ((⌈(1 + ε₀) * c * L⌉₊ : ℕ) : ℝ) ≤ (1 + ε₀) * c * L + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    rw [div_le_iff₀ hL]
    have hswallow : EW + 1 ≤ ε / 2 * L := by
      have := (div_le_iff₀ (show (0:ℝ) < ε / 2 by linarith)).mp hbg
      linarith
    calc (∫⁻ ω, (chernoffStoppingTime (k := k) δ ω : ℝ≥0∞) ∂P).toReal
        ≤ EW + ((1 + ε₀) * c * L + 1) := by linarith
      _ = (EW + 1) + (1 + ε₀) * c * L := by ring
      _ ≤ ε / 2 * L + (c + ε / 2) * L := by
          have h2 : (1 + ε₀) * c * L ≤ (c + ε / 2) * L :=
            mul_le_mul_of_nonneg_right hinfl hL.le
          linarith
      _ = (c + ε) * L := by ring
