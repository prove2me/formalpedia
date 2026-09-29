-- Prove2me | Definitions.Def_Algebra_SmoothWindows_GaussianWindow
-- name    : Algebra_SmoothWindows_GaussianWindow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T17:03:05.126379+00:00
-- url     : https://prove2.me/theorems/2dbebe5c-0205-441f-ae39-3adc2ad6caf9
-- title:
--   Aether Catalog definitions — Algebra_SmoothWindows_GaussianWindow
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SmoothWindows.GaussianWindow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SmoothWindows/GaussianWindow.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators

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

namespace SmoothWindows

open Complex Real MeasureTheory FourierTransform

/-! ## The Gaussian window -/

/-- The **Gaussian window** of width `s`: `g_s(t) = exp(-π t²/s²)`. -/
noncomputable def gaussWin (s t : ℝ) : ℝ := Real.exp (-π * t ^ 2 / s ^ 2)

/-- The complex-valued Gaussian window, as an element of the representation space `ℝ → ℂ`. -/
noncomputable def gaussC (s : ℝ) : ℝ → ℂ := fun t => (gaussWin s t : ℂ)










/-! ## Fourier intertwining of translation and modulation -/



/-! ## Fourier self-duality of the Gaussian window -/


/-! ## Gabor atoms: a sidelobe-free transfer function -/

/-- The **Gabor atom** with Gaussian window: `T_a M_b g_s`, a smooth probe of the point `(a, b)`
of phase space. -/
noncomputable def gaborAtom (s a b : ℝ) : ℝ → ℂ := transOp a (modOp b (gaussC s))








end SmoothWindows


