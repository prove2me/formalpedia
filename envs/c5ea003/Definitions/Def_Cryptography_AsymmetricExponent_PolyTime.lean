-- Prove2me | Definitions.Def_Cryptography_AsymmetricExponent_PolyTime
-- name    : Cryptography_AsymmetricExponent_PolyTime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:03:17.698406+00:00
-- url     : https://prove2.me/theorems/77f9a8b4-76f8-4251-be71-6bf90200ce31
-- title:
--   Aether Catalog definitions — Cryptography_AsymmetricExponent_PolyTime
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AsymmetricExponent.PolyTime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AsymmetricExponent/PolyTime.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core

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

namespace AsymmetricExponent

/-- Square-and-multiply modular exponentiation. -/
def powMod (m a : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | (n + 1) =>
      let h := powMod m a ((n + 1) / 2)
      if (n + 1) % 2 = 0 then h * h % m else h * h % m * (a % m) % m
  decreasing_by omega

/-- The number of recursive calls made by `powMod` on exponent `n`. -/
def powModSteps : ℕ → ℕ
  | 0 => 0
  | (n + 1) => powModSteps ((n + 1) / 2) + 1
  decreasing_by omega





end AsymmetricExponent


