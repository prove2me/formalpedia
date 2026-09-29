-- Prove2me | Definitions.Def_Applications_BSD_FrobeniusTrace
-- name    : Applications_BSD_FrobeniusTrace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:32:05.604523+00:00
-- url     : https://prove2.me/theorems/95a2c08b-be2c-4160-a1a9-f75c035f6dc4
-- title:
--   Aether Catalog definitions — Applications_BSD_FrobeniusTrace
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BSD.FrobeniusTrace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BSD/FrobeniusTrace.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BSD Research Cycle — The Frobenius Trace Recurrence and the Sato–Tate Angle

For an elliptic curve `E / ℚ` with good reduction at `p`, the number of points over
the extension field `𝔽_{p^n}` is governed by the Frobenius eigenvalues `α, β` (the
reciprocal roots of the local L-factor, with `α + β = a_p` and `α β = p`):

  `#E(𝔽_{p^n}) = p^n + 1 - (αⁿ + βⁿ)`.

The *power sums* `sₙ = αⁿ + βⁿ` are the traces of the `n`-th power of Frobenius.
This file isolates two structural pillars of the local BSD theory that complement
`LocalFactor.lean`:

* the **linear recurrence** `s_{n+2} = a_p · s_{n+1} - p · s_n` (with `s₀ = 2`,
  `s₁ = a_p`), Newton's identity for the degree-two characteristic polynomial, which
  lets the entire tower of point counts be computed from `a_p` and `p` alone; and
* the **Sato–Tate parametrization** `a_p = 2√p · cos θ`, the angular form of the
  Hasse bound that is the substrate of the Sato–Tate equidistribution conjecture.

It closes with the archimedean bound `‖αⁿ + βⁿ‖ ≤ 2 (√p)ⁿ` that the Riemann
Hypothesis over finite fields imposes on every power sum.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the whole sequence of point counts is *rigid* — it is the
  unique solution of a second-order linear recurrence with constant coefficients
  `a_p, p`, so `a_p` (equivalently `#E(𝔽_p)`) determines `#E(𝔽_{p^n})` for all `n`.
Experiment (Experimenter): define `traceSeq a p` by the recurrence and prove
  `traceSeq a p n = αⁿ + βⁿ` by two-step induction, using Newton's identity
  `power_sum_recurrence` (a pure `ring` fact once `α+β=a`, `αβ=p` are substituted).
Analysis (Analyst): the base cases `s₀ = 2` (not `1`!) and `s₁ = a` are forced by
  `α⁰ + β⁰ = 2`; getting `s₀` wrong is the classic off-by-one in Newton's identities.
  The Sato–Tate angle is well defined exactly because `|a| ≤ 2√p` puts `a/(2√p)` in
  `[-1, 1]`, the domain of `arccos`.
Critique (Critic): the norm bound `‖αⁿ + βⁿ‖ ≤ 2 (√p)ⁿ` must use only `‖α‖ = ‖β‖ =
  √p` (the RH input), not the algebraic relations, so it is the genuinely analytic
  half and stays valid for all `n` including the degenerate `n = 0` (`2 ≤ 2`).
Synthesis (PI): recurrence + angle + norm bound package the local point-count tower
  underlying the Euler product; the recurrence is the computational engine, the angle
  is the equidistribution coordinate, and the bound is the RH constraint.
-/

namespace BSD.FrobeniusTrace

open Complex

/-
**Newton's recurrence for power sums.**  For `α, β` with sum `a` and product `p`,
the power sums `αⁿ + βⁿ` satisfy the degree-two linear recurrence
`s_{n+2} = a · s_{n+1} - p · s_n`.
-/

/-- The **Frobenius trace sequence** `sₙ`: the unique solution of the recurrence
`s_{n+2} = a · s_{n+1} - p · s_n` with `s₀ = 2`, `s₁ = a`.  It equals the power sum
`αⁿ + βⁿ` of the Frobenius eigenvalues (`traceSeq_eq_power_sum`). -/
def traceSeq (a p : ℂ) : ℕ → ℂ
  | 0 => 2
  | 1 => a
  | (n + 2) => a * traceSeq a p (n + 1) - p * traceSeq a p n




/-
**The trace sequence computes the Frobenius power sums.**  If `α + β = a` and
`α β = p`, then `traceSeq a p n = αⁿ + βⁿ` for all `n`.
-/

/-- The point count `#E(𝔽_{p^n}) = p^n + 1 - sₙ` expressed through the trace
sequence, so the entire tower is determined by `a_p` and `p`. -/
def pointCount (a p : ℂ) (n : ℕ) : ℂ := p ^ n + 1 - traceSeq a p n

/-
At `n = 0` the trace-sequence point count vanishes (`p⁰ + 1 - 2 = 0`).
-/

/-
At `n = 1` the point count is `p + 1 - a_p`, the defining relation for `a_p`.
-/

/-
**Sato–Tate angle.**  Under the Hasse bound `a² ≤ 4p` (with `0 < p`), the trace of
Frobenius can be written `a = 2√p · cos θ` for an angle `θ ∈ [0, π]`.  This is the
angular coordinate in which the Sato–Tate conjecture predicts equidistribution.
-/

/-
**RH bound on the power sums.**  If both Frobenius eigenvalues lie on the circle
of radius `√p` (the Riemann Hypothesis over finite fields), then every power sum is
bounded: `‖αⁿ + βⁿ‖ ≤ 2 (√p)ⁿ`.
-/

end BSD.FrobeniusTrace


