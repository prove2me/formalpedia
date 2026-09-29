-- Prove2me | Theorems.Thm_EulerTwoSquares_repFinset_card_eq_two
-- name    : EulerTwoSquares.repFinset_card_eq_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:32:22.651164+00:00
-- url     : https://prove2.me/theorems/f2690409-dcb0-4ec7-bcbc-7f30c310883b
-- title:
--   The representation count of an eligible semiprime is exactly two.
-- statement:
--   **The representation count of an eligible semiprime is exactly two.**  For distinct primes
--   `p ≡ q ≡ 1 [MOD 4]` the finite set of normalised two-square representations of `p*q` has
--   cardinality `2`.
--
--   ```lean
--   theorem EulerTwoSquares.repFinset_card_eq_two(hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
--       (hpq : p ≠ q) : (repFinset (p * q)).card = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/EulerTwoSquaresRepCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/EulerTwoSquaresRepCount.lean#L64

-- Thm stub generated from Algebra/EulerTwoSquaresRepCount.lean
import Mathlib
import Definitions.Def_Algebra_EulerTwoSquaresRepCount

/-!
# The representation count, as a finite cardinality

`EulerTwoSquares.exactly_two_reps` describes the representations of `p*q` as a list of four
ordered integer pairs.  Here we package the same information as a *cardinality*: the finite
set of normalised representations

`repFinset n = {(a,b) : 0 < a ≤ b, a² + b² = n}`

has exactly two elements when `n = p*q` for distinct primes `p ≡ q ≡ 1 [MOD 4]`.  This is the
form in which the eligibility statistics of a factorisation experiment are actually measured.
-/

open EulerTwoSquares

variable {p q : ℕ}

theorem EulerTwoSquares.repFinset_card_eq_two(hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) : (repFinset (p * q)).card = 2 := by sorry
