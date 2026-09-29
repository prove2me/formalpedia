-- Prove2me | Theorems.Thm_MobiusDiscriminantSecondOrder_hankel_not_eventually_signed
-- name    : MobiusDiscriminantSecondOrder.hankel_not_eventually_signed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:09:03.036103+00:00
-- url     : https://prove2.me/theorems/f972d87d-a2f4-4fe0-a619-e44cdba45511
-- title:
--   Not Filter.eventually signed.
-- statement:
--   **Not Filter.eventually signed.**  When `p, r > 0` and `D(0) ≠ 0`, the Hankel
--   determinant is strictly positive at infinitely many indices and strictly
--   negative at infinitely many indices.  This generalizes the Fibonacci/Cassini
--   obstruction to *every* second-order recurrence with `r/p > 0`.
--
--   ```lean
--   theorem MobiusDiscriminantSecondOrder.hankel_not_eventually_signed{a : ℕ → ℝ} {p q r : ℝ}
--       (hrec : ∀ n : ℕ, p * a (n + 2) = q * a (n + 1) + r * a n)
--       (hp : 0 < p) (hr : 0 < r) (hD0 : hankel a 0 ≠ 0) :
--       (∀ N : ℕ, ∃ n ≥ N, 0 < hankel a n) ∧ (∀ N : ℕ, ∃ n ≥ N, hankel a n < 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MobiusDiscriminantSecondOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MobiusDiscriminantSecondOrder.lean#L133

-- Thm stub generated from Novelty/MobiusDiscriminantSecondOrder.lean
import Mathlib
import Definitions.Def_Novelty_MobiusDiscriminantSecondOrder

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

open MobiusDiscriminantSecondOrder

theorem MobiusDiscriminantSecondOrder.hankel_not_eventually_signed{a : ℕ → ℝ} {p q r : ℝ}
    (hrec : ∀ n : ℕ, p * a (n + 2) = q * a (n + 1) + r * a n)
    (hp : 0 < p) (hr : 0 < r) (hD0 : hankel a 0 ≠ 0) :
    (∀ N : ℕ, ∃ n ≥ N, 0 < hankel a n) ∧ (∀ N : ℕ, ∃ n ≥ N, hankel a n < 0) := by sorry
