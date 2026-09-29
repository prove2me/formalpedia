-- Prove2me | Definitions.Def_Tropical_JacobiSignedMultiplicative
-- name    : Tropical_JacobiSignedMultiplicative
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:31:47.468799+00:00
-- url     : https://prove2.me/theorems/8421dd41-d7e8-4f1f-a54c-82e5e8efabad
-- title:
--   Aether Catalog definitions — Tropical_JacobiSignedMultiplicative
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.JacobiSignedMultiplicative`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/JacobiSignedMultiplicative.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound

/-!
# Multiplicativity of the Jacobi-signed circle count and the semiprime Weil floor

The Jacobi-signed circle count is defined for an arbitrary modulus `n` by weighting the
circle `x² + y² = 1` over `ZMod n` with the *Jacobi symbol* `(x / n)`.  Summing the `y`'s
away, this is the character sum

`WZ n = ∑_{x : ZMod n} (x(1-x²) / n)`.

Main results.

* `JacSign.jchar_mul` : `x ↦ (x / n)` is multiplicative on `ZMod n`.
* `JacSign.WZ_mul` : `WZ (m n) = WZ m · WZ n` for coprime moduli — the Chinese remainder
  theorem turns the circle count into a **symmetric product over the factors**.
* `JacSign.WZ_prime` : for a prime modulus the Jacobi-signed count is the Legendre
  character sum `W p` of the core file.
* `JacSign.WZ_semiprime` : `WZ (p q) = W p · W q` for distinct primes.
* `JacSign.WZ_semiprime_sq_le` : `WZ (p q) ^ 2 ≤ 16 · p q`, i.e. `|WZ N| ≤ 4 √N`:
  **the semiprime Weil floor.**  The signal available to a factoring witness is
  `O(√N)` against a search space of size `N`.
* `JacSign.WZ_semiprime_eq_zero_of_three_mod_four` : if either prime is `≡ 3 (mod 4)`
  the whole statistic vanishes.
-/

open Finset

namespace JacSign

/-- The Jacobi symbol as a `ℤ`-valued function on `ZMod n`. -/
def jchar (n : ℕ) [NeZero n] (x : ZMod n) : ℤ := jacobiSym (x.val : ℤ) n

/-- The Jacobi-signed circle count for an arbitrary modulus. -/
noncomputable def WZ (n : ℕ) [NeZero n] : ℤ := ∑ x : ZMod n, jchar n (x * (1 - x ^ 2))









/-! ### The geometric statistic for a composite modulus -/

/-- The Jacobi-signed circle count of the paper, for an arbitrary modulus: the points of
`x² + y² = 1` over `ZMod n`, weighted by the Jacobi symbol `(x / n)`. -/
noncomputable def circleWeightZ (n : ℕ) [NeZero n] : ℤ :=
  ∑ x : ZMod n, ∑ y : ZMod n, if x ^ 2 + y ^ 2 = 1 then jchar n x else 0






end JacSign


