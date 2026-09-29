-- Prove2me | Definitions.Def_Novelty_FloatBackwardErrorHorner
-- name    : Novelty_FloatBackwardErrorHorner
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:33.737203+00:00
-- url     : https://prove2.me/theorems/cab9361d-1021-4239-b390-cd856ddb354b
-- title:
--   Aether Catalog definitions — Novelty_FloatBackwardErrorHorner
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FloatBackwardErrorHorner`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FloatBackwardErrorHorner.lean by skeleton subtraction
import Mathlib

/-!
# Backward-error semantics for rounded polynomial evaluation

This file develops the *semantics* half of the conjecture

> every finite floating-point execution of a polynomial dynamical system that
> avoids overflow and exceptional values can be translated into an exact real
> pseudo-orbit whose local defect is bounded by a compositional expression in the
> unit roundoff and the intermediate magnitudes.

The model of computation is the standard IEEE-754 model *in the absence of
overflow, underflow and exceptional values* (`RoundingModel`): each arithmetic
operation returns the exact result multiplied by `(1 + e)` with `|e| ≤ u`, where
`u` is the unit roundoff (`2^-53` for binary64).  This is exactly the hypothesis
"the execution avoids overflow and exceptional values"; nothing else about the
bit-level format is used, so every conclusion applies verbatim to binary32,
binary64, and to any faithfully-rounded arithmetic.

Main results:

* `hornerFl_backward` — **backward-error semantics**: the rounded Horner
  evaluation of a polynomial with coefficient list `as` at a point `x` is the
  *exact* real evaluation at the same point `x` of a perturbed polynomial whose
  coefficients differ from `as` by at most the relative factor
  `gamma u (2 * as.length) = (1 + u) ^ (2 * as.length) - 1`.
* `hornerFl_forward_defect` — the resulting *local defect certificate*
  `|fl-eval − exact-eval| ≤ gamma u (2 n) * Σ |aᵢ| |x|ᵢ`, a compositional
  expression in the unit roundoff and the intermediate magnitudes.
* `gamma_le_classical` — the classical Higham bound
  `(1+u)^k − 1 ≤ k u / (1 − k u)` whenever `k u < 1`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): floating-point execution of a polynomial iteration is
not merely "approximately" the real iteration; it is *exactly* a real iteration
of a nearby polynomial, so the correct interface to a shadowing theorem is a
coefficientwise backward-error statement, not a forward error bound.
Experiment (Experimenter): formalize an abstract rounding model and prove the
backward statement by induction on the coefficient list, then *derive* the
forward defect from it.  The derivation succeeded, confirming that the forward
bound carries strictly less information than the backward one.
Analysis (Analyst): the exponent `2 n` (two roundings per Horner step) is forced
by the induction: each step multiplies all previously perturbed coefficients by
`(1+e₁)(1+e₂)`.  A sharper `2i`-graded version is true but the uniform bound is
the one consumed by the shadowing layer.
Critique (Critic): the model is unconditional in `u ≥ 0`; no hypothesis `u < 1`
is needed for the backward statement, and the classical `k u/(1 - k u)` form is
proved separately under its natural hypothesis `k u < 1`.
-- !-- End Lab Notes -- !--
-/

namespace Novelty.FloatBackwardError

open scoped BigOperators

/-- The standard model of IEEE-754 arithmetic in an execution free of overflow,
underflow and exceptional values: every operation is computed exactly and then
perturbed by a relative error of at most the unit roundoff `u`. -/
structure RoundingModel where
  /-- Unit roundoff (`2 ^ (-53)` for IEEE binary64). -/
  u : ℝ
  u_nonneg : 0 ≤ u
  /-- Machine addition. -/
  add : ℝ → ℝ → ℝ
  /-- Machine multiplication. -/
  mul : ℝ → ℝ → ℝ
  /-- Machine subtraction. -/
  sub : ℝ → ℝ → ℝ
  add_spec : ∀ a b, ∃ e : ℝ, |e| ≤ u ∧ add a b = (a + b) * (1 + e)
  mul_spec : ∀ a b, ∃ e : ℝ, |e| ≤ u ∧ mul a b = a * b * (1 + e)
  sub_spec : ∀ a b, ∃ e : ℝ, |e| ≤ u ∧ sub a b = (a - b) * (1 + e)

/-- The classical error-accumulation quantity `γ_k = (1+u)^k − 1`. -/
def gamma (u : ℝ) (k : ℕ) : ℝ := (1 + u) ^ k - 1





/-! ### Horner evaluation, exact and rounded -/

/-- Exact real Horner evaluation of the polynomial `a₀ + a₁ x + a₂ x² + ⋯`. -/
def hornerR : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: as, x => a + x * hornerR as x

/-- Rounded (floating-point) Horner evaluation in the model `M`. -/
def hornerFl (M : RoundingModel) : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: as, x => M.add a (M.mul x (hornerFl M as x))

/-- The magnitude functional `Σ |aᵢ| |x|ⁱ` controlling the intermediate sizes. -/
def hornerAbs (as : List ℝ) (x : ℝ) : ℝ := hornerR (as.map abs) |x|









/-! ### Sharpness of the defect certificate

The factor `γ_{2n}(u)` is linear in `u` to first order.  The following worst-case
model (every operation rounds *up* by exactly the maximal relative amount) shows
that no bound of order `u²` can hold: the defect really is of size `u` times the
magnitude functional, so the certificate is sharp up to the constant `3`. -/

/-- The adversarial rounding model in which every operation incurs the maximal
relative error `+u`.  It satisfies the IEEE-754 relative-error axioms. -/
def uniformModel (u : ℝ) (hu : 0 ≤ u) : RoundingModel where
  u := u
  u_nonneg := hu
  add a b := (a + b) * (1 + u)
  mul a b := a * b * (1 + u)
  sub a b := (a - b) * (1 + u)
  add_spec a b := ⟨u, by rw [abs_of_nonneg hu], rfl⟩
  mul_spec a b := ⟨u, by rw [abs_of_nonneg hu], rfl⟩
  sub_spec a b := ⟨u, by rw [abs_of_nonneg hu], rfl⟩



end Novelty.FloatBackwardError


