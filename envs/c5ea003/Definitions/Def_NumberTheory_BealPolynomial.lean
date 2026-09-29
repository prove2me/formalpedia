-- Prove2me | Definitions.Def_NumberTheory_BealPolynomial
-- name    : NumberTheory_BealPolynomial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:05:57.639471+00:00
-- url     : https://prove2.me/theorems/a367ec80-39d8-4022-9190-8157b0b1eb08
-- title:
--   Aether Catalog definitions — NumberTheory_BealPolynomial
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.BealPolynomial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/BealPolynomial.lean by skeleton subtraction
import Mathlib

/-!
# The function-field analogue of Beal's conjecture is a theorem

Over the integers Beal's conjecture is open.  Over a polynomial ring `k[X]` with `k` a field of
characteristic zero the analogous statement is *provable*, via the Mason–Stothers theorem (the
polynomial `abc` theorem), which is available in Mathlib as `Polynomial.flt_catalan`.

The main results are:

* `Beal.polynomial_beal`: if `a ^ x + b ^ y = c ^ z` in `k[X]` with `x, y, z ≥ 3`, all three
  polynomials nonzero, and at least one of them non-constant, then `a, b, c` have a common
  prime (irreducible) factor — the exact analogue of Beal's conjecture.
* `Beal.polynomial_beal_coprime`: equivalently, a coprime solution has only constant entries.
* `Beal.PolynomialBealConjecture` / `Beal.polynomialBealConjecture_holds`: the statement packaged
  in the same shape as `Beal.BealConjecture`, and its proof.

Together with `Beal.abc_implies_beal_counterexamples_bounded`, this exhibits the same mechanism
(`abc`/Mason–Stothers plus the hyperbolicity inequality `1/x + 1/y + 1/z ≤ 1`) in the two
settings: over function fields the inequality is already enough, over `ℤ` one needs the
(conjectural) `abc` inequality with an error term.
-/

namespace Beal

open Polynomial

variable {k : Type*} [Field k] [CharZero k]





/-- The analogue of `Beal.IsBealSolution` over `k[X]`. -/
def IsPolynomialBealSolution (a b c : k[X]) (x y z : ℕ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧ a ^ x + b ^ y = c ^ z

/-- The analogue of `Beal.BealConjecture` over `k[X]`, for non-constant solutions. -/
def PolynomialBealConjecture (k : Type*) [Field k] [CharZero k] : Prop :=
  ∀ (a b c : k[X]) (x y z : ℕ), IsPolynomialBealSolution a b c x y z →
    (a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0) →
    ∃ p : k[X], Prime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c



end Beal


