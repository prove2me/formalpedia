-- Prove2me | solution 1 for SmoothWindows.fourier_gaussC
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T21:22:11.864989+00:00
-- url     : https://prove2.me/submissions/48419726-33bc-4cc8-8da4-4f07e1d9c050

-- Sol generated from Algebra/SmoothWindows/GaussianWindow.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators
import Definitions.Def_Algebra_SmoothWindows_GaussianWindow

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
theorem solution{s : ℝ} (hs : 0 < s) :
    𝓕 (gaussC s) = fun ξ : ℝ => (s : ℂ) * gaussC (1 / s) ξ := by
  have hb : (0 : ℝ) < 1 / s ^ 2 := by positivity
  have hbc : (0 : ℝ) < (((1 / s ^ 2 : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; exact hb
  have hrw : gaussC s = fun x : ℝ => Complex.exp (-(π : ℂ) * ((1 / s ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ 2) :=
    by
    funext x
    rw [gaussC, gaussWin, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  rw [hrw, fourier_gaussian_pi hbc]
  funext ξ
  have hsqrt : (((1 / s ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((1 / s : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, Real.sqrt_sq hs.le, one_div]
  rw [hsqrt, gaussC, gaussWin, Complex.ofReal_exp]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [show ((1 / s : ℝ) : ℂ) = 1 / (s : ℂ) by push_cast; ring]
  rw [one_div_one_div]
  congr 1
  push_cast
  field_simp
