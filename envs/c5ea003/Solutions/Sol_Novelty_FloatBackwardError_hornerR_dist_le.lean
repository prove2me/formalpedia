-- Prove2me | solution 1 for Novelty.FloatBackwardError.hornerR_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:09:00.998416+00:00
-- url     : https://prove2.me/submissions/eddf60b2-9233-4590-b2b6-b6c34cc509a1

-- Sol generated from Novelty/FloatBackwardErrorHorner.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Theorems.Thm_Novelty_FloatBackwardError_hornerAbs_cons

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

open Novelty.FloatBackwardError

open scoped BigOperators







/-! ### Horner evaluation, exact and rounded -/












/-! ### Sharpness of the defect certificate

The factor `γ_{2n}(u)` is linear in `u` to first order.  The following worst-case
model (every operation rounds *up* by exactly the maximal relative amount) shows
that no bound of order `u²` can hold: the defect really is of size `u` times the
magnitude functional, so the certificate is sharp up to the constant `3`. -/





open Novelty.FloatBackwardError in
theorem solution{c : ℝ} {bs as : List ℝ}
    (h : List.Forall₂ (fun b a => |b - a| ≤ c * |a|) bs as) (x : ℝ) :
    |hornerR bs x - hornerR as x| ≤ c * hornerAbs as x := by
  induction h with
  | nil => simp [hornerR, hornerAbs]
  | @cons b a bs as hba _ ih =>
      have hx : (0:ℝ) ≤ |x| := abs_nonneg x
      have key : hornerR (b :: bs) x - hornerR (a :: as) x
          = (b - a) + x * (hornerR bs x - hornerR as x) := by
        simp [hornerR]; ring
      rw [key, hornerAbs_cons]
      calc |(b - a) + x * (hornerR bs x - hornerR as x)|
          ≤ |b - a| + |x| * |hornerR bs x - hornerR as x| := by
            refine (abs_add_le _ _).trans ?_
            simp [abs_mul]
        _ ≤ c * |a| + |x| * (c * hornerAbs as x) := by
            have := ih
            nlinarith [hx, ih, hba]
        _ = c * (|a| + |x| * hornerAbs as x) := by ring
