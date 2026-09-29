-- Prove2me | Definitions.Def_Novelty_MobiusDiscriminantSecondOrder
-- name    : Novelty_MobiusDiscriminantSecondOrder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:43.045025+00:00
-- url     : https://prove2.me/theorems/749037b2-78a0-4ead-91ed-ac68a7d28ce9
-- title:
--   Aether Catalog definitions — Novelty_MobiusDiscriminantSecondOrder
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MobiusDiscriminantSecondOrder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MobiusDiscriminantSecondOrder.lean by skeleton subtraction
import Mathlib

/-!
# The Hankel law of the Möbius discriminant: the exact second-order invariant

The companion development `MobiusDiscriminantQuantitative.lean` studied the
scalar **Möbius discriminant** `Δ = γβ − αδ` of a *first-order* multiplicative
recurrence `(α n + β)·a(n+1) = (γ n + δ)·a(n)` and showed, among other things,
that no *coefficient-only* discriminant can govern the sign of the pointwise
Hankel determinant `D(n) = a(n)·a(n+2) − a(n+1)²` for a **second-order**
recurrence — the Fibonacci numbers, with constant coefficients `p = q = r = 1`,
have `D(n) = (−1)^{n+1}`, which is `+1` and `−1` infinitely often.

This file goes deeper and *explains* that obstruction structurally.  The correct
invariant is not a number attached to the coefficients but an **exact first-order
multiplicative law for the Hankel determinant itself**:

> For any sequence obeying `p·a(n+2) = q·a(n+1) + r·a(n)`,
> `p·D(n+1) = −r·D(n)`  (`hankel_recurrence`),
> hence `pⁿ·D(n) = (−r)ⁿ·D(0)`  (`hankel_closed_form`).

Thus the Hankel determinant is a *geometric* sequence with ratio `−r/p`.  Its
sign is governed by `(−r)ⁿ·D(0)`, so:

* when `r < 0` (and `p, D(0)` fixed sign) the sign is Filter.eventually constant;
* when `r > 0` the sign **alternates**, and can never be Filter.eventually one-signed
  (`hankel_sign_alternates`, `hankel_not_eventually_signed`).

The Fibonacci/Cassini obstruction is exactly the case `p = r = 1 > 0`, recovered
here as a corollary (`fib_cassini_from_hankel`,
`fib_discriminant_not_eventually_signed'`).  So the first-order theory is special
not because the second-order Hankel determinant is chaotic, but because for
second order the multiplier `−r/p` is *negative* whenever `r > 0`.

## Lab Notes
-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  The Fibonacci sign-oscillation found in the
  previous cycle is not evidence that "no invariant exists"; it is evidence that
  the second-order Hankel determinant obeys its *own* recurrence with a possibly
  negative multiplier.  Conjecture: `D` satisfies a first-order linear recurrence
  with constant coefficients determined by `p` and `r` alone (independent of `q`).
* **Experiment (Experimenter).**  Computed `D(n+1)` vs `−(r/p)·D(n)` for the
  sequence `a(n+2)=3a(n+1)−2a(n)` (`r=−2`): agreement `D(n) = −6·2ⁿ`.  For
  Fibonacci (`r=1`): `D = −1,1,−1,1,…`.  Both fit `pⁿ D(n) = (−r)ⁿ D(0)`.
  Proven by a two-line `linear_combination` and an induction.
* **Analysis (Analyst).**  The multiplier is `−r/p`, *independent of `q`* — the
  drift coefficient `q` cancels.  This isolates `r` (the "memory depth" term) as
  the single parameter controlling curvature sign dynamics, mirroring how `Δ`
  was the single first-order invariant.  When `r>0` the multiplier is negative,
  forcing alternation; the previous cycle's obstruction is precisely this.
* **Critique (Critic).**  Is `hankel_recurrence` trivial?  No: it is a genuine
  cancellation identity requiring both recurrence instances.  Is
  `hankel_sign_alternates` vacuous?  No: it needs `D(0) ≠ 0`, and we prove
  `D(n) ≠ 0` for all `n` from the closed form; the Fibonacci instance witnesses
  `D(0) = −1 ≠ 0`, so the hypothesis is satisfiable.  No circular references:
  every proof uses only lemmas declared strictly above it.
* **Synthesis (PI).**  A clean dichotomy: sign of `r` (relative to `p`) governs
  whether the second-order Hankel determinant is Filter.eventually signed
  (`r/p < 0`) or perpetually alternating (`r/p > 0`).
-/

namespace MobiusDiscriminantSecondOrder

/-- The pointwise Hankel determinant of a real sequence. -/
def hankel (a : ℕ → ℝ) (n : ℕ) : ℝ := a n * a (n + 2) - a (n + 1) ^ 2






/-! ## The Fibonacci / Cassini instance, recovered from the general law -/




end MobiusDiscriminantSecondOrder


