-- Prove2me | Definitions.Def_Probability_QuadraticDichotomy
-- name    : Probability_QuadraticDichotomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:40.773284+00:00
-- url     : https://prove2.me/theorems/c9f629fb-9ad7-4ea0-a498-0e8047403f2d
-- title:
--   Aether Catalog definitions — Probability_QuadraticDichotomy
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.QuadraticDichotomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/QuadraticDichotomy.lean by skeleton subtraction
import Mathlib
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

namespace FactoringLab

/-! ## 1.  The symmetric-function identity -/


/-! ## 2.  The `N`-only side of the dichotomy -/



/-! ## 3.  The recovery side: an explicit quadratic for `p + q` -/

/-- The candidate polynomial for `p + q`: its coefficients are computed from the
public data `N` and `T = f(N)` (and the fixed `a, b, c`) alone. -/
noncomputable def sumCandidatePoly (a b c N T : ℤ) : Polynomial ℤ :=
  C (a * c) * X ^ 2 + C (a * b * N + b * c) * X
    + C (a ^ 2 * N ^ 2 + (b ^ 2 - 2 * (a * c)) * N + c ^ 2 - T)







/-! ## 4.  The dichotomy -/


/-! ## 5.  The affine and linear families as special cases -/


end FactoringLab


