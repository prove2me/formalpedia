-- Prove2me | Definitions.Def_NumberTheory_WallSunSunPrimes
-- name    : NumberTheory_WallSunSunPrimes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:19.649224+00:00
-- url     : https://prove2.me/theorems/d51e73a3-4c26-495f-907f-6876544e9d42
-- title:
--   Aether Catalog definitions — NumberTheory_WallSunSunPrimes
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.WallSunSunPrimes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/WallSunSunPrimes.lean by skeleton subtraction
import Mathlib
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

/-!
# Wall–Sun–Sun primes: certified elementary results

The existence of a Wall–Sun–Sun prime is an open problem.  Accordingly, this file does not
assert existence.  It gives a direct natural-number definition, certifies a finite search bound,
and disproves two tempting but false conjectures about the relation with Fermat's Last Theorem.

For a prime `p ≠ 2, 5`, quadratic reciprocity says `(5/p) = 1` exactly when
`p % 5 ∈ {1,4}`. Thus `fibonacciIndex p` is `p - (p|5)`, represented in `ℕ`.
-/

namespace WallSunSun

set_option maxHeartbeats 2000000 in
section

/-- The natural-number form of `p - (p|5)` for primes away from `2` and `5`. -/
def fibonacciIndex (p : ℕ) : ℕ :=
  if p % 5 = 1 ∨ p % 5 = 4 then p - 1 else p + 1

/-- A Wall–Sun–Sun prime (also called a Fibonacci–Wieferich prime). -/
def IsWallSunSunPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ^ 2 ∣ Nat.fib (fibonacciIndex p)









end

end WallSunSun


