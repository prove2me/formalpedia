-- Prove2me | Definitions.Def_Applications_CycleGameThreshold_Constant
-- name    : Applications_CycleGameThreshold_Constant
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:04.015657+00:00
-- url     : https://prove2.me/theorems/2f428bf6-bca5-4050-98c4-05c2b2b1735d
-- title:
--   Aether Catalog definitions — Applications_CycleGameThreshold_Constant
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CycleGameThreshold.Constant`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CycleGameThreshold/Constant.lean by skeleton subtraction
import Mathlib

/-!
# The threshold exponent and constant for the Maker–Breaker `C_k`-game

The mission claims that for fixed `k ≥ 4` the threshold bias of the Maker–Breaker
`C_k`-game on `K_n` is `c_k · n^{(k-2)/(k-1)}`, where

  `c_k = ((k-1) · (2(k-1)/k)^{k-2})^{1/(k-1)}`.

This file establishes the exact algebraic/analytic backbone of that formula:

* `gameExponent k = (k-2)/(k-1)` and `maxDensity k = (k-1)/(k-2)` are reciprocal
  (`exponent_density_duality`), and the exponent is strictly increasing in `k`,
  bounded above by `1` (`gameExponent_strictMonoOn`, `gameExponent_lt_one`).
* the constant `c_k` (defined via `Real.rpow`) is positive and satisfies the defining
  closed form `c_k^{k-1} = (k-1)·(2(k-1)/k)^{k-2}` (`thresholdConst_pow`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the exponent `(k-2)/(k-1)` and density `(k-1)/(k-2)` are
reciprocals; `c_k` is a genuine positive real whose `(k-1)`-st power recovers the
bracketed expression.  Surprising sub-claim tested numerically: `c_k` is *not* monotone
— it rises to `≈2.15` near `k≈10..20` then decreases towards its limit `2`.
Experiment (Experimenter): `gameExponent k = 1 - 1/(k-1)`, immediately giving strict
monotonicity and the bound `< 1`.  Numerics: `c_4≈1.890, c_5≈2.012, c_10≈2.152,
c_100≈2.060, c_1000≈2.010`, consistent with `c_k → 2`.
Analysis (Analyst): the `rpow` closed form needs `base > 0`; positivity of `k-1` and
`2(k-1)/k` for `k ≥ 4` supplies this.  `(x^{1/(k-1)})^{k-1} = x` is `Real.rpow` algebra
via `rpow_natCast` and `rpow_natCast_mul`.
Critique (Critic): none of these are definitional — `thresholdConst_pow` is a real
`rpow` identity requiring positivity side-conditions, and `gameExponent_strictMonoOn`
is a genuine monotonicity statement, not `rfl`.
Synthesis: the formula `c_k · n^{(k-2)/(k-1)}` is well posed, with reciprocal
exponent/density and a positive constant obeying its defining polynomial identity.
-/

namespace CycleGameThreshold

open Real

/-- The Bednarska–Łuczak threshold exponent `(k-2)/(k-1)` for the `C_k`-game. -/
noncomputable def gameExponent (k : ℝ) : ℝ := (k - 2) / (k - 1)

/-- The maximum 2-density `(k-1)/(k-2)` of the cycle `C_k`. -/
noncomputable def maxDensity (k : ℝ) : ℝ := (k - 1) / (k - 2)

/-- The threshold constant `c_k = ((k-1)·(2(k-1)/k)^{k-2})^{1/(k-1)}`. -/
noncomputable def thresholdConst (k : ℕ) : ℝ :=
  (((k : ℝ) - 1) * (2 * ((k : ℝ) - 1) / (k : ℝ)) ^ (k - 2)) ^ ((1 : ℝ) / ((k : ℝ) - 1))

/-
**Exponent–density duality.**  The game exponent and the maximum 2-density are
reciprocal: `gameExponent k * maxDensity k = 1` for `k ≠ 1, 2`.
-/

/-
The game exponent is strictly increasing for `k > 1`.
-/

/-
The game exponent is strictly below `1` for `k > 1`.
-/

/-
The base of the threshold constant is positive for `k ≥ 4`.
-/

/-
The threshold constant is positive for `k ≥ 4`.
-/

/-
**Closed form of the constant.**  Raising `c_k` to the power `k-1` recovers the
defining bracketed expression `(k-1)·(2(k-1)/k)^{k-2}`.
-/

end CycleGameThreshold


