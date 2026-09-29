-- Prove2me | Theorems.Thm_FactoringLab_quadratic_degenerate_monomial
-- name    : FactoringLab.quadratic_degenerate_monomial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:32:26.308846+00:00
-- url     : https://prove2.me/theorems/200dc085-c6b7-47c2-8d5f-ebf9f458d0de
-- title:
--   In the degenerate case the coefficient vector forces `F` to be a monomial.
-- statement:
--   In the degenerate case the coefficient vector forces `F` to be a monomial.
--
--   ```lean
--   theorem FactoringLab.quadratic_degenerate_monomial{a b c N : ℤ} (hN : N ≠ 0)
--       (h1 : a * c = 0) (h2 : a * b * N + b * c = 0) :
--       (a = 0 ∧ b = 0) ∨ (a = 0 ∧ c = 0) ∨ (b = 0 ∧ c = 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/QuadraticDichotomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/QuadraticDichotomy.lean#L53

-- Thm stub generated from Probability/QuadraticDichotomy.lean
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

theorem FactoringLab.quadratic_degenerate_monomial{a b c N : ℤ} (hN : N ≠ 0)
    (h1 : a * c = 0) (h2 : a * b * N + b * c = 0) :
    (a = 0 ∧ b = 0) ∨ (a = 0 ∧ c = 0) ∨ (b = 0 ∧ c = 0) := by sorry
