-- Prove2me | Theorems.Thm_FactoringLab_factor_recovery_from_totient_nat
-- name    : FactoringLab.factor_recovery_from_totient_nat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:30:45.4343+00:00
-- url     : https://prove2.me/theorems/315971bc-5ffe-4d5d-87d0-cacedbb25c68
-- title:
--   The circular side of the dichotomy (φ version).
-- statement:
--   **The circular side of the dichotomy (φ version).**  The same closed-form
--   recovery from `N` and Euler's totient value.
--
--   ```lean
--   theorem FactoringLab.factor_recovery_from_totient_nat{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hne : p ≠ q) (hpq : p ≤ q) :
--       let N : ℤ := (p * q : ℕ)
--       let s : ℤ := N + 1 - (Nat.totient (p * q) : ℤ)
--       ((s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = (p : ℤ)) ∧
--         ((s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = (q : ℤ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/MultiplicativeDichotomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/MultiplicativeDichotomy.lean#L104

-- Thm stub generated from Probability/MultiplicativeDichotomy.lean
import Mathlib
import Definitions.Def_Probability_SymmetryCircularity
/-
# The multiplicative dichotomy

A sharpening of the structural-orthogonality thesis for the classical
multiplicative invariants of a semiprime `N = p*q` (`p ≠ q` prime).  Each such
invariant falls on exactly one of two sides:

* **Constant side (no information).**  The number of divisors, the number of
  distinct prime factors and the Möbius value are *literally constant* on the
  set of semiprimes: `4`, `2`, `1`.  They cannot distinguish any two
  semiprimes, let alone their factors
  (`FactoringLab.constant_invariants_carry_no_information`).
* **Circular side (as hard as factoring).**  The sum of divisors `σ₁` and
  Euler's totient `φ` both reveal `p + q` from `N`, and `(N, p+q)` recovers the
  factorization in closed form
  (`FactoringLab.factor_recovery_from_sigma`).  An invariant on this side does
  not help: computing it is already a factoring algorithm.

There is no third option among these classical invariants — which is exactly
the empirical "N-only or circular" pattern of the lab experiments.
-/

open FactoringLab

open ArithmeticFunction

/-! ### The constant side -/





/-! ### The circular side -/

theorem FactoringLab.factor_recovery_from_totient_nat{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpq : p ≤ q) :
    let N : ℤ := (p * q : ℕ)
    let s : ℤ := N + 1 - (Nat.totient (p * q) : ℤ)
    ((s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = (p : ℤ)) ∧
      ((s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = (q : ℤ)) := by sorry
