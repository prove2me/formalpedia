-- Prove2me | Definitions.Def_Cryptography_LWE_DiscreteGaussian
-- name    : Cryptography_LWE_DiscreteGaussian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:18:56.309256+00:00
-- url     : https://prove2.me/theorems/aadc6e98-00a2-43fe-a1ce-d381eb28074a
-- title:
--   Aether Catalog definitions — Cryptography_LWE_DiscreteGaussian
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.DiscreteGaussian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/DiscreteGaussian.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Discrete Gaussian and the Analytic Core of the LWE Reduction

The worst-case-to-average-case reduction for Learning with Errors is built on the
**Gaussian measure** on lattices.  The reduction samples lattice points from a
*discrete Gaussian* and argues that, once the width `s` exceeds the *smoothing
parameter*, the distribution behaves like the continuous Gaussian.  This module
formalises the pointwise Gaussian weight `ρ_s(x) = exp(-π x² / s²)`, its basic
shape (positivity, boundedness, evenness, monotone decay, scaling), and packages
the finitely supported discrete Gaussian as a genuine probability distribution.

## Main results

* `rho_pos`, `rho_le_one`, `rho_zero` — the Gaussian weight lands in `(0, 1]`
  with peak `1` at the origin.
* `rho_even`, `rho_scale` — evenness and the width-normalisation identity
  `ρ_s(x) = ρ₁(x / s)`.
* `rho_antitone_abs` — the weight decays monotonically in `|x|`, the shape fact
  behind Gaussian tail bounds.
* `discreteGaussian_sum_one` — the finitely supported discrete Gaussian is a
  probability distribution (masses sum to `1`).
* `discreteGaussian_nonneg`, `discreteGaussian_le_one` — its masses lie in
  `[0, 1]`.

## References

* Micciancio & Regev, "Worst-Case to Average-Case Reductions Based on Gaussian
  Measures", SIAM J. Comput. 2007.
* Banaszczyk, "New bounds in some transference theorems in the geometry of
  numbers", Math. Ann. 1993.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the analytic backbone of the Regev reduction reduces
to two facts about `ρ_s`: it is a peaked, monotonically decaying weight, and its
finite renormalisation is a probability law.  Everything quantitative
(smoothing, tail mass) is a consequence of monotone decay.

Experiment (Experimenter): define `ρ_s(x) = exp(-π x²/s²)`; prove the shape
lemmas; define `gaussianMass`/`discreteGaussian` over a `Finset ℝ` of lattice
points; show the masses are a probability distribution.

Analysis (Analyst): the scaling identity `ρ_s(x) = ρ₁(x/s)` holds *even at
`s = 0`* because Lean's `/0 = 0`; we keep it unconditional.  Monotone decay needs
`s > 0` and reduces (after `exp_le_exp`) to `gcongr` once the sign is flipped —
`gcongr` refuses negative coefficients, so the neg-rewrite is load-bearing.

Critique (Critic): `discreteGaussian_sum_one` is the non-trivial theorem — it
uses `Finset.sum_div` and positivity of the normaliser; not `rfl`.  The `[0,1]`
bounds are honest (require nonempty support / membership).

Synthesis (PI): these feed the "error width vs. smoothing parameter" comparison
consumed by `RegevParameters.lean`.
-- !-- Lab Notes -- !--
-/

open Finset BigOperators Real

noncomputable section

/-- The Gaussian weight of width `s` at `x`: `ρ_s(x) = exp(-π x² / s²)`. -/
def rho (s x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2 / s ^ 2)







/-! ## The discrete Gaussian as a probability distribution -/

/-- The total Gaussian mass of a finite set of lattice points. -/
def gaussianMass (s : ℝ) (pts : Finset ℝ) : ℝ := ∑ x ∈ pts, rho s x


/-- The discrete Gaussian probability mass at `x`, supported on `pts`. -/
def discreteGaussian (s : ℝ) (pts : Finset ℝ) (x : ℝ) : ℝ :=
  rho s x / gaussianMass s pts




end


