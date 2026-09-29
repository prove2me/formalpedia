-- Prove2me | Definitions.Def_EML_QuadraticApproxRate
-- name    : EML_QuadraticApproxRate
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:43.058817+00:00
-- url     : https://prove2.me/theorems/72f277fb-6e9e-48b9-80d8-a60887e26e5a
-- title:
--   Aether Catalog definitions — EML_QuadraticApproxRate
-- statement:
--   Definition bundle for the Aether Catalog module `EML.QuadraticApproxRate`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/QuadraticApproxRate.lean by skeleton subtraction
import Mathlib
/-
# EML Interpolation Theory: An Explicit Jackson-Type Rate for x² on [0,1]

This file constructs a concrete, single-exponential **EML network** (a finite
composition of `exp`, `+`, `*` and scalars) that approximates the map `x ↦ x²`
on `[0,1]` with an **explicit, vanishing error bound**.

The network is
`emlQuadApprox h x = (2 / h²) · (exp (h·x) − 1 − h·x)`,
which is the rescaled second-order forward difference of `exp`. Taylor's theorem
gives the error bound `|emlQuadApprox h x − x²| ≤ (4/9)·h` uniformly on `[0,1]`,
and choosing `h = 1/n` produces a width-`n` family with rate `O(1/n)`.

This is a fully explicit witness for the Jackson-type rate conjectured in the
mission: a Lipschitz target (`x²` on `[0,1]`) approximated by an EML network
whose accuracy degrades only linearly in the inverse width.

## Main results
- `emlQuadApprox_error`: uniform error bound `|emlQuadApprox h x − x²| ≤ (4/9)·h`.
- `emlQuadApprox_rate`: width-`n` rate `|emlQuadApprox (1/n) x − x²| ≤ 4/(9·n)`.
- `emlQuadApprox_tendsto`: the construction converges to `x²` pointwise on `[0,1]`.
-/

noncomputable section

open Real

/-- The EML network approximating `x²`: the rescaled second-order increment of `exp`.
`emlQuadApprox h x = (2 / h²) · (exp (h·x) − 1 − h·x)`. Built only from `exp`,
addition, multiplication and scalars, it is an EML function. -/
def emlQuadApprox (h x : ℝ) : ℝ := (2 / h ^ 2) * (Real.exp (h * x) - 1 - h * x)

/-
**Key Taylor estimate.** For `u ∈ [0,1]`, the exponential exceeds its
quadratic Taylor polynomial by at most `(2/9)·u³`.
-/

/-
**Explicit uniform error bound.** On `[0,1]`, with step `0 < h ≤ 1`, the EML
network `emlQuadApprox h` approximates `x²` to within `(4/9)·h`.
-/

/-
**Width-`n` Jackson-type rate.** Choosing `h = 1/n`, the width-`n` EML network
approximates `x²` on `[0,1]` with error at most `4/(9·n)`, i.e. rate `O(1/n)`.
-/

/-
**Convergence.** For each fixed `x ∈ [0,1]`, the width-`n` EML networks converge
to `x²` as `n → ∞`.
-/

/-
-- !-- Lab Notes -- !--

## Hypothesis (Hypothesizer)
The mission asks for an EML network of width `n` approximating `x²` on `[0,1]`
with explicit error bounds. Conjecture: the rescaled second-order forward
difference of the exponential, `(2/h²)(exp(hx) − 1 − hx)`, is an EML function that
approximates `x²` with error `O(h)`, hence with rate `O(1/n)` for `h = 1/n`.

## Experiment (Experimenter)
Numerical check (Float) of the error `(2/h²)(exp(hx)−1−hx) − x²`:
  h = 0.1 , x = 1   → 0.0342   ( ≤ (4/9)·0.1  = 0.0444 )
  h = 0.01, x = 1   → 0.00334  ( ≤ (4/9)·0.01 = 0.00444 )
The bound `(4/9)·h` holds and is not far from tight at `x = 1`.

## Analysis (Analyst)
Writing `u = h·x`, algebra gives
  emlQuadApprox h x − x² = (2/h²)·(exp u − 1 − u − u²/2).
Taylor's theorem (`Real.exp_bound` at `n = 3`) bounds `|exp u − (1+u+u²/2)|` by
`(2/9)|u|³`. Substituting `|u| = h·x ≤ 1` collapses the `h²` denominator and
yields `(4/9)·h·x³ ≤ (4/9)·h`. This is "true but the constant is route-dependent":
the cleanest provable constant from `Real.exp_bound` is `4/9`.

## Critique (Critic)
- Not trivial: the proof needs Taylor's theorem, the `u = h·x` substitution, and
  `field_simp`/`ring` to clear the `h²` denominator.
- Boundary cases: `h = 0` is excluded (division by zero); `x ∈ [0,1]` is needed so
  that `|u| ≤ 1` (the hypothesis of `Real.exp_bound`).
- The rate is genuine: `emlQuadApprox_rate` gives a quantitative `O(1/n)` bound,
  not an existential, surpassing bare universal-approximation guarantees.

## Synthesis (PI)
A single-exponential EML network realises a Jackson-type `O(1/n)` rate for `x²`
on `[0,1]`, with a fully explicit constant `4/9`. This is the concrete numeric
companion to the abstract Stone–Weierstrass density in `EML.StoneWeierstrassApprox`.
-/
end


