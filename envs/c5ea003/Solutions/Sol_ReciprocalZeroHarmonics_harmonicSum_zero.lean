-- Prove2me | solution 1 for ReciprocalZeroHarmonics.harmonicSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:30:23.513373+00:00
-- url     : https://prove2.me/submissions/7e35a13f-8eb6-4ffd-8905-74703dc0cb6b

-- Sol generated from Algebra/ReciprocalZeroHarmonics/Core.lean
import Mathlib
import Definitions.Def_Algebra_ReciprocalZeroHarmonics_Core

/-!
# Reciprocal-Zero Harmonics I: the multiplicity-sensitive, conjugate-symmetric harmonic sum

This file defines the *harmonic sum* of a multiset of nonzero complex numbers,

  `H(s) = Σ_{ρ ∈ s} 1/ρ`,

together with the finite-window ("cutoff `T`") version

  `H(Z, T) = Σ_{ρ ∈ Z, |Im ρ| ≤ T} 1/ρ`

used in the Reciprocal-Zero Harmonics programme.  Working with a `Multiset` rather than a
`Finset` makes the statistic **multiplicity sensitive**: a zero of multiplicity `m` contributes
`m/ρ`, exactly as in the classical sum `Σ_ρ 1/ρ` over the zeros of `ζ`.

## Main results

* `harmonicSum_eq_neg_deriv_div` — **Vieta invariance.** If `P = C a · ∏_{r ∈ s} (X - r)` with
  `a ≠ 0` and no root is `0`, then `H(s) = -P'(0)/P(0)`.  The reciprocal sum of a root multiset
  is therefore a *ratio of two coefficients*, not a transcendental function of the individual
  roots.
* `conj_harmonicSum` and `windowSum_real` — **conjugate pairing makes `H` real.**  If the zero
  multiset is invariant under complex conjugation then every symmetric window `|Im ρ| ≤ T`
  is again conjugation invariant, and `H(Z,T)` is a real number.
* `criticalZero_pair_inv` — the conjugate pair `1/2 ± i t` contributes the *positive real*
  quantity `1/(1/4 + t²)`; this is the renormalisation that converts a conditionally organised
  complex sum into an absolutely convergent real spectral statistic.
* `harmonicSum_pairedOrdinates` — the window sum over a conjugate-paired family of critical-line
  zeros with ordinates `S` equals `Σ_{t ∈ S} 1/(1/4 + t²)`.
* `harmonicSum_pairedOrdinates_pos` — that statistic is strictly positive as soon as `S ≠ 0`,
  so `H` can vanish only on empty windows.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** `Σ_{|Im ρ| ≤ T} 1/ρ` is a *real* number for any conjugation
  symmetric zero multiset, and equals a Vieta-type coefficient ratio whenever the multiset is
  the full root multiset of a polynomial.
* **Experiment (Experimenter).** The Vieta identity is proved by `Multiset.induction_on` on the
  root multiset using `derivative_mul`: the inductive step is exactly the logarithmic-derivative
  recursion `P'(0)/P(0) = -1/a + Q'(0)/Q(0)` for `P = (X - a)·Q`.  Reality is proved by showing
  the conjugation-invariance of the window filter.
* **Analysis (Analyst).** Two independent mechanisms appear: an *algebraic* one (Vieta) that
  identifies the value, and an *analytic/symmetry* one (conjugation) that constrains it to `ℝ`.
  Both are insensitive to repetitions, i.e. they hold verbatim for multisets with multiplicity.
* **Critique (Critic).** The hypothesis `0 ∉ s` is genuinely needed: `0⁻¹ = 0` in Lean, so the
  identity `H = -P'(0)/P(0)` fails without it (both sides are then unrelated).  The reality
  statement is not vacuous — `harmonicSum_pairedOrdinates_pos` exhibits nonzero values.
-/

open ReciprocalZeroHarmonics

open Polynomial

/-! ## The harmonic sum of a multiset of zeros -/










/-! ## Conjugate symmetry: `H` is a real spectral statistic -/




open Classical





/-! ## The critical-line pairing -/












open ReciprocalZeroHarmonics in
@[simp] theorem solution: harmonicSum 0 = 0 := by simp [harmonicSum]
