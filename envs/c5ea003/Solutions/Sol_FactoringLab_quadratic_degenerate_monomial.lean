-- Prove2me | solution 1 for FactoringLab.quadratic_degenerate_monomial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:30.590367+00:00
-- url     : https://prove2.me/submissions/3c737572-7c7f-4b69-abdd-fef3ce01ccbf

-- Sol generated from Probability/QuadraticDichotomy.lean
import Mathlib
import Definitions.Def_Probability_QuadraticDichotomy
import Definitions.Def_Probability_SymmetryCircularity
/-
# The Quadratic Multiplicative Dichotomy (Factoring Lab, Phase A v19c — cycle 2)

Partially closing **Conjecture 3** of `FUTURE_DIRECTIONS.md`.

The previous cycle proved the dichotomy for the *affine* family `f(r) = r + c`
(`FactoringLab.affine_invariant_dichotomy`): such an invariant is either `N` in
disguise (`c = 0`) or it hands over `p + q` and hence, by
`FactoringLab.recovery_from_sum`, the complete factorization.

Here the same dichotomy is established for the *entire quadratic family*: `f`
multiplicative with `f(r) = a r² + b r + c` at primes, so that
`T = f(N) = F(p) F(q)` for a semiprime `N = pq`.  The two sides are:

* **`FactoringLab.quadratic_invariant_N_only`** — in the degenerate case
  `a c = 0 ∧ a b N + b c = 0` the value is the explicit function
  `T = a²N² + b²N + c²` of `N` alone.  (The degenerate case is exactly
  "`F` is a monomial `a X²`, `b X` or `c`", which the proof extracts.)
* **`FactoringLab.quadratic_invariant_determines_sum`** — otherwise `p + q` is a
  root of the *explicit nonzero* integer polynomial
  `Q = (ac) X² + (abN + bc) X + (a²N² + (b² − 2ac)N + c² − T)`
  whose coefficients are computed from `N` and `T` only.  Since `deg Q ≤ 2`
  there are at most two candidate values of `p + q`, and each candidate yields
  a candidate factorization in closed form.

So the invariant is either `N`-only or a factoring algorithm in disguise,
with at most a factor-two search in between; there is no intermediate
"partially informative" behaviour in the quadratic family.  The key algebraic
step is the symmetric-function identity `quadratic_invariant_identity`, which
expresses `F(p)F(q)` in terms of `N = pq` and `s = p + q` alone — the exact
mechanism the conjecture predicted.
-/

open Polynomial

open FactoringLab

/-! ## 1.  The symmetric-function identity -/


/-! ## 2.  The `N`-only side of the dichotomy -/



/-! ## 3.  The recovery side: an explicit quadratic for `p + q` -/








/-! ## 4.  The dichotomy -/


/-! ## 5.  The affine and linear families as special cases -/



open FactoringLab in
theorem solution{a b c N : ℤ} (hN : N ≠ 0)
    (h1 : a * c = 0) (h2 : a * b * N + b * c = 0) :
    (a = 0 ∧ b = 0) ∨ (a = 0 ∧ c = 0) ∨ (b = 0 ∧ c = 0) := by
  rcases mul_eq_zero.1 h1 with ha | hc
  · subst ha
    by_cases hb : b = 0
    · exact Or.inl ⟨rfl, hb⟩
    · have : b * c = 0 := by simpa using h2
      rcases mul_eq_zero.1 this with hb' | hc'
      · exact absurd hb' hb
      · exact Or.inr (Or.inl ⟨rfl, hc'⟩)
  · subst hc
    by_cases hb : b = 0
    · exact Or.inr (Or.inr ⟨hb, rfl⟩)
    · have : a * b * N = 0 := by simpa using h2
      rcases mul_eq_zero.1 this with hab | hN'
      · rcases mul_eq_zero.1 hab with ha' | hb'
        · exact Or.inr (Or.inl ⟨ha', rfl⟩)
        · exact absurd hb' hb
      · exact absurd hN' hN
