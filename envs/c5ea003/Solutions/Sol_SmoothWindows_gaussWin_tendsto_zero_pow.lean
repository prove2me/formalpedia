-- Prove2me | solution 1 for SmoothWindows.gaussWin_tendsto_zero_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T21:25:42.726245+00:00
-- url     : https://prove2.me/submissions/ab29d3c9-0609-4482-a692-188e25043b4b

-- Sol generated from Algebra/SmoothWindows/GaussianWindow.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators
import Definitions.Def_Algebra_SmoothWindows_GaussianWindow
import Theorems.Thm_SmoothWindows_gaussWin_pos

/-!
# Smooth windows II: the Gaussian window and its Fourier duality

Building on the Heisenberg/Weyl algebra of `Algebra.SmoothWindows.GaborOperators`, this file
introduces the **Gaussian window**

  `g_s(t) = exp(-π t² / s²)`,  `s > 0`,

and establishes the structural facts that make it the canonical smooth replacement for the
rectangular window of `Algebra.ReciprocalZeroHarmonics.WindowDichotomy`.

## Main results

* `gaussWin_translate_mul` — **the Gaussian window algebra is closed under products of
  translates**: `g_s(t-a) · g_s(t-b) = exp(-π(a-b)²/(2s²)) · g_{s/√2}(t - (a+b)/2)`.  Two Gaussian
  probes at different positions multiply to a *single* Gaussian probe at the midpoint, with an
  exponentially small overlap constant.  Nothing of this kind holds for rectangular windows.
* `fourier_transOp`, `fourier_modOp` — the Fourier transform **intertwines** translation and
  modulation: `𝓕 T_a = χ(-a·) 𝓕` and `𝓕 M_b = T_b 𝓕`.  Together with the Weyl relation this is
  the modulation/translation identity on the frequency side.
* `fourier_gaussC` — **Fourier self-duality with width inversion**: `𝓕 g_s = s · g_{1/s}`.  The
  Gaussian family is a fixed family of the Fourier transform; the width parameter is inverted,
  which is the exact form of the time–frequency uncertainty trade-off for this family.
* `fourier_gaborAtom` — the transform of a Gabor atom `T_a M_b g_s` is a modulated Gaussian
  centred at the frequency `b`; `norm_fourier_gaborAtom` shows its modulus is *exactly* a
  Gaussian bump, hence **strictly unimodal and sidelobe-free** (`norm_fourier_gaborAtom_lt` and
  `norm_fourier_gaborAtom_strictAnti`).
* `gaussWin_tendsto_zero_pow` — the Gaussian window has rapid (super-polynomial) decay, the
  Schwartz property that makes it usable as a smooth analysing window.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** Replacing the sharp cutoff by `g_s` should trade a discontinuous
  transfer function with slowly decaying sidelobes for a strictly unimodal, exponentially
  decaying one, *without* losing any of the exact algebraic identities.
* **Experiment (Experimenter).** The product identity is the polarisation identity
  `(t-a)² + (t-b)² = 2(t-m)² + (a-b)²/2` fed through `Real.exp_add`.  Self-duality is obtained by
  specialising Mathlib's `fourier_gaussian_pi` at `b = 1/s²`, the delicate part being the complex
  power `b^{1/2}` which must be identified with the real square root.
* **Analysis (Analyst).** The three phenomena — closure under products, self-duality, unimodality
  of the transform — are all consequences of a single fact: the Gaussian is the unique (up to the
  Heisenberg action) minimiser of the uncertainty product, hence a *fixed vector* for the
  metaplectic action.  The rectangular window has none of these properties.
* **Critique (Critic).** Every statement carries `0 < s`; at `s = 0` the definition degenerates
  (`x/0 = 0` in Lean gives the constant window `1`), which is why the hypothesis is kept
  explicit rather than derived.
-/

open SmoothWindows

open Complex Real MeasureTheory FourierTransform

/-! ## The Gaussian window -/












/-! ## Fourier intertwining of translation and modulation -/



/-! ## Fourier self-duality of the Gaussian window -/


/-! ## Gabor atoms: a sidelobe-free transfer function -/










open SmoothWindows in
theorem solution{s : ℝ} (hs : 0 < s) (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => t ^ n * gaussWin s t) Filter.atTop (nhds 0) := by
  have hc : 0 < π / s ^ 2 := by positivity
  -- compare with `u^n e^{-u}` after the substitution `u = π t²/s²`
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have harg : Filter.Tendsto (fun t : ℝ => π / s ^ 2 * t ^ 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc (Filter.tendsto_pow_atTop (by norm_num))
  have hcomp : Filter.Tendsto (fun t : ℝ => (π / s ^ 2 * t ^ 2) ^ n *
      Real.exp (-(π / s ^ 2 * t ^ 2))) Filter.atTop (nhds 0) := by
    simpa [Function.comp] using hbase.comp harg
  refine squeeze_zero' ?_ ?_ hcomp
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    have := gaussWin_pos s t
    positivity
  · filter_upwards [Filter.eventually_ge_atTop (max 1 (s ^ 2 / π))] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
    have ht2 : s ^ 2 / π ≤ t := le_trans (le_max_right _ _) ht
    have hs2 : (0 : ℝ) < s ^ 2 := by positivity
    have hpi := Real.pi_pos
    have hst : s ^ 2 ≤ t * π := by rwa [div_le_iff₀ hpi] at ht2
    have hkey : t ≤ π / s ^ 2 * t ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hs2]
      nlinarith
    have hpow : t ^ n ≤ (π / s ^ 2 * t ^ 2) ^ n := pow_le_pow_left₀ (by linarith) hkey n
    have hexp : gaussWin s t = Real.exp (-(π / s ^ 2 * t ^ 2)) := by
      rw [gaussWin]; congr 1; field_simp
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
