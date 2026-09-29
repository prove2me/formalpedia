-- Prove2me | Theorems.Thm_Beal_polynomial_beal
-- name    : Beal.polynomial_beal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:24:42.878178+00:00
-- url     : https://prove2.me/theorems/c2fbed86-0429-4ab4-b583-3ce385d187c0
-- title:
--   The polynomial Beal theorem.
-- statement:
--   **The polynomial Beal theorem.**  Over a field of characteristic zero, any solution of
--   `a ^ x + b ^ y = c ^ z` with `x, y, z ≥ 3` and not all of `a, b, c` constant has a common
--   irreducible factor.
--
--   ```lean
--   theorem Beal.polynomial_beal{a b c : k[X]} {x y z : ℕ}
--       (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
--       (heq : a ^ x + b ^ y = c ^ z)
--       (hnonconst : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0) :
--       ∃ p : k[X], Prime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/BealPolynomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/BealPolynomial.lean#L50

-- Thm stub generated from NumberTheory/BealPolynomial.lean
import Mathlib
import Definitions.Def_NumberTheory_BealPolynomial

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

open Beal

open Polynomial

variable {k : Type*} [Field k] [CharZero k]

theorem Beal.polynomial_beal{a b c : k[X]} {x y z : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hnonconst : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0) :
    ∃ p : k[X], Prime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c := by sorry
