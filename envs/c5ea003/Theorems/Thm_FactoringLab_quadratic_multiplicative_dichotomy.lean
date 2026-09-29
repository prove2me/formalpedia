-- Prove2me | Theorems.Thm_FactoringLab_quadratic_multiplicative_dichotomy
-- name    : FactoringLab.quadratic_multiplicative_dichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:32:39.59352+00:00
-- url     : https://prove2.me/theorems/c23912ad-d0fd-4a3d-8114-799b98aa85a3
-- title:
--   The quadratic multiplicative dichotomy.
-- statement:
--   **The quadratic multiplicative dichotomy.**  Let `f` be the multiplicative
--   invariant with `f(r) = a r² + b r + c` at primes, and let `N = pq` (`p ≤ q`) be
--   a semiprime with value `T = f(N) = F(p)F(q)`.  Exactly one of the following
--   happens.
--
--   *Degenerate case* (`ac = 0` and `abN + bc = 0`, i.e. `F` a monomial):
--     `T = a²N² + b²N + c²` is a function of `N` alone and carries no information
--     about the factorization.
--   *Nondegenerate case*: `p + q` is one of at most two roots of the explicit
--     polynomial `Q` built from `(N, T)`, and from the correct root the factors are
--     recovered in closed form as `(s ∓ √(s² − 4N))/2`.
--
--   There is no intermediate behaviour: a quadratic multiplicative invariant is
--   either `N` in disguise or a factoring algorithm in disguise (up to a two-way
--   branch).
--
--   ```lean
--   theorem FactoringLab.quadratic_multiplicative_dichotomy{a b c p q : ℤ} (hpq : p ≤ q) (hN : p * q ≠ 0) :
--       let N := p * q
--       let T := (a * p ^ 2 + b * p + c) * (a * q ^ 2 + b * q + c)
--       ((a * c = 0 ∧ a * b * N + b * c = 0) → T = a ^ 2 * N ^ 2 + b ^ 2 * N + c ^ 2) ∧
--         (¬ (a * c = 0 ∧ a * b * N + b * c = 0) →
--           let Q := sumCandidatePoly a b c N T
--           Q ≠ 0 ∧ Multiset.card Q.roots ≤ 2 ∧ (p + q) ∈ Q.roots ∧
--             ((p + q) - (Int.sqrt ((p + q) ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
--             ((p + q) + (Int.sqrt ((p + q) ^ 2 - 4 * N) : ℤ)) / 2 = q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/QuadraticDichotomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/QuadraticDichotomy.lean#L144

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



/-! ## 3.  The recovery side: an explicit quadratic for `p + q` -/








/-! ## 4.  The dichotomy -/

theorem FactoringLab.quadratic_multiplicative_dichotomy{a b c p q : ℤ} (hpq : p ≤ q) (hN : p * q ≠ 0) :
    let N := p * q
    let T := (a * p ^ 2 + b * p + c) * (a * q ^ 2 + b * q + c)
    ((a * c = 0 ∧ a * b * N + b * c = 0) → T = a ^ 2 * N ^ 2 + b ^ 2 * N + c ^ 2) ∧
      (¬ (a * c = 0 ∧ a * b * N + b * c = 0) →
        let Q := sumCandidatePoly a b c N T
        Q ≠ 0 ∧ Multiset.card Q.roots ≤ 2 ∧ (p + q) ∈ Q.roots ∧
          ((p + q) - (Int.sqrt ((p + q) ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
          ((p + q) + (Int.sqrt ((p + q) ^ 2 - 4 * N) : ℤ)) / 2 = q) := by sorry
