-- Prove2me | Theorems.Thm_AsymmetricExponent_powMod_eq
-- name    : AsymmetricExponent.powMod_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:51.232219+00:00
-- url     : https://prove2.me/theorems/15cbe5e5-49c6-4c94-a241-49502628584e
-- title:
--   Correctness of square-and-multiply.
-- statement:
--   **Correctness of square-and-multiply.**
--
--   ```lean
--   theorem AsymmetricExponent.powMod_eq(m a : ℕ) : ∀ n : ℕ, powMod m a n = a ^ n % m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/PolyTime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/PolyTime.lean#L39

-- Thm stub generated from Cryptography/AsymmetricExponent/PolyTime.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Definitions.Def_Cryptography_AsymmetricExponent_PolyTime

/-!
# `Q(a) = a^(N-1) mod N` is cheap: a verified logarithmic-cost algorithm

The FETQ quantity is interesting only because it costs nothing to compute.
This file makes that precise inside Lean: a binary (square-and-multiply)
modular exponentiation routine is defined, proved **correct**, and its
recursion depth is proved to be at most the binary length `Nat.size` of the
exponent.  Computing `Q(a)` therefore costs `O(log N)` modular multiplications
— no factorisation, no aggregation over many `a`.

Main results.

* `AsymmetricExponent.powMod_eq` — `powMod m a n = a^n % m` (strong induction on
  the exponent).
* `AsymmetricExponent.powModSteps_le_size` — the number of recursive halvings
  is at most `Nat.size n`.
* `AsymmetricExponent.fetq_eq_powMod` and
  `AsymmetricExponent.fetq_cost_logarithmic` — the FETQ quantity is computed by
  this routine at logarithmic cost.
-/

open AsymmetricExponent

theorem AsymmetricExponent.powMod_eq(m a : ℕ) : ∀ n : ℕ, powMod m a n = a ^ n % m := by sorry
