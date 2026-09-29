-- Prove2me | solution 1 for WindowOptimumFinite.exists_window_optimum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:27:10.42976+00:00
-- url     : https://prove2.me/submissions/3e2efcb2-6e80-4548-a156-cd43ffd6a1c1

-- Sol generated from Algebra/WindowOptimumFinite.lean
import Mathlib
import Definitions.Def_Algebra_ProductDialWeighting
import Definitions.Def_Algebra_WindowOptimumFinite
import Theorems.Thm_ProductDialWeighting_harmonicAmp_pos
import Theorems.Thm_ProductDialWeighting_harmonic_window_sum
import Theorems.Thm_ProductDialWeighting_log_sq_div_tendsto_zero
/-
# The window is stronger, not shifted: finiteness of the count-dial optimum

Formal core of experiment **577** (paper 227), verdict part
(`WINDOW-STRONGER-NOT-SHIFTED`) and dispersion bookkeeping.

## The verdict to be explained

The pre-registered alternative `H1` was a *scale shift*: that the informative
quadratic-residue window moves outwards as the cutoff `B` grows, so that some
larger `B` would beat `B = 400`.  All four shift candidates failed, and the
measured sweep of the equal-weight count dial

  `B = 400 : R² = .3207`, `4000 : .0241`, `4·10⁴ : .0150`, `10⁵ : .0000`,
  `10⁶ : .0277`

instead *decays*.  The weighted dial, by contrast, is monotone and saturates.

## What is proved here

Working in the harmonic amplitude model of `ProductDialWeighting`:

* `WindowOptimumFinite.countR2_le_countScore` — the count dial's explained
  variance is bounded by the ambient-free score `H_n² / n`.
* `WindowOptimumFinite.countScore_tendsto_zero` — that score tends to `0`:
  there is no escape to larger windows.
* `WindowOptimumFinite.exists_window_optimum` — **the refutation of the scale
  shift**: the count-dial score attains a *global maximum at a finite window*
  `B*`.  Enlarging the window past `B*` can never help; the optimum does not run
  off to infinity.
* `WindowOptimumFinite.weighted_never_hurts` — the contrasting behaviour of the
  weighted dial: it is monotone in the window, so its "optimum" is the whole
  population, and by the saturation theorem it is already essentially attained
  at a small window.
* `WindowOptimumFinite.weighted_saturated_at_400` — at the published window the
  weighted dial captures at least `99.75%` of what any larger window can.
* `WindowOptimumFinite.harmonic_weightedR2_le` — the matching *lower* bound:
  a window of size `n` never explains more than `1 - 1/(8n)`, so the saturation
  rate is of order `1/n` exactly and the window size is a tolerance parameter,
  not a scale parameter.
* `WindowOptimumFinite.reading_ratio` — the exact algebra relating the two
  dispersion readings ("fraction of raw overdispersion" versus "fraction of
  excess above Poisson"): their ratio is `(D-1)/D`, *independent of the size of
  the reduction*.
* `WindowOptimumFinite.readings_consistent` — the two measured dial rows
  (`33.43% / 42.06%` and `48.51% / 61.00%`) imply the same baseline dispersion
  to within `0.03`, which is why both readings may be quoted for the same
  population.
-/

open WindowOptimumFinite

open Finset Filter Topology ProductDialWeighting

/-! ## 1. The ambient-free count score -/


theorem countScore_nonneg (n : ℕ) : 0 ≤ countScore n := by
  unfold countScore; positivity

theorem countScore_one : countScore 1 = 1 := by
  simp [countScore, harmonicAmp]


/-- The score obeys the logarithmic bound. -/
theorem countScore_le_log {n : ℕ} (hn : 0 < n) :
    countScore n ≤ (1 + Real.log n) ^ 2 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum : ∑ i ∈ range n, harmonicAmp i ≤ 1 + Real.log n := by
    rw [harmonic_window_sum]
    exact harmonic_le_one_add_log n
  have hnum0 : 0 ≤ ∑ i ∈ range n, harmonicAmp i :=
    Finset.sum_nonneg (fun i _ => le_of_lt (harmonicAmp_pos i))
  rw [countScore, div_le_div_iff₀ hnpos hnpos]
  have hsq : (∑ i ∈ range n, harmonicAmp i) ^ 2 ≤ (1 + Real.log n) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right hsq (le_of_lt hnpos)

/-- **No escape to larger windows**: the count score tends to `0`. -/
theorem countScore_tendsto_zero : Tendsto countScore atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall (fun n => countScore_nonneg n)) ?_
    log_sq_div_tendsto_zero
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact countScore_le_log hn




/-! ### 1b. The saturation rate is exactly of order `1/n`

The upper bound `1 - 1/n ≤ weightedR²` of `harmonic_weightedR2_ge` is matched by a
lower bound of the same order, so "how large a window do I need" is a question
about the *tolerance* only, never about the size of the ambient population. -/




/-! ## 2. Dispersion bookkeeping: the two readings of one reduction -/






open WindowOptimumFinite in
theorem solution:
    ∃ B : ℕ, 1 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → countScore n ≤ countScore B := by
  -- beyond some `m`, the score is below its value at the single-prime window
  have h := countScore_tendsto_zero
  rw [Metric.tendsto_atTop] at h
  obtain ⟨m, hm⟩ := h 1 one_pos
  have hbeyond : ∀ n : ℕ, m ≤ n → countScore n < countScore 1 := by
    intro n hn
    have := hm n hn
    rw [Real.dist_eq, sub_zero, countScore_one] at *
    exact lt_of_abs_lt this
  -- maximise over the finite range `[1, m]`
  have hne : (Icc 1 (max m 1)).Nonempty := ⟨1, mem_Icc.mpr ⟨le_refl 1, le_max_right m 1⟩⟩
  obtain ⟨B, hB, hBmax⟩ := Finset.exists_max_image (Icc 1 (max m 1)) countScore hne
  refine ⟨B, (mem_Icc.mp hB).1, fun n hn => ?_⟩
  rcases le_or_gt n (max m 1) with hle | hgt
  · exact hBmax n (mem_Icc.mpr ⟨hn, hle⟩)
  · have hnm : m ≤ n := le_trans (le_max_left m 1) (le_of_lt hgt)
    have h1 : countScore n < countScore 1 := hbeyond n hnm
    have h2 : countScore 1 ≤ countScore B :=
      hBmax 1 (mem_Icc.mpr ⟨le_refl 1, le_max_right m 1⟩)
    linarith
