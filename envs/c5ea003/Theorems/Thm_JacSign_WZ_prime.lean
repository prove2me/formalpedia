-- Prove2me | Theorems.Thm_JacSign_WZ_prime
-- name    : JacSign.WZ_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:36:24.829061+00:00
-- url     : https://prove2.me/theorems/679abc4d-b085-432e-9b5e-297894b93db2
-- title:
--   For a prime modulus, the Jacobi-signed circle count is the Legendre character sum.
-- statement:
--   For a prime modulus, the Jacobi-signed circle count is the Legendre character sum.
--
--   ```lean
--   theorem JacSign.WZ_prime(p : ℕ) [Fact p.Prime] : WZ p = W p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedMultiplicative.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedMultiplicative.lean#L107

-- Thm stub generated from Tropical/JacobiSignedMultiplicative.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

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

open JacSign

theorem JacSign.WZ_prime(p : ℕ) [Fact p.Prime] : WZ p = W p := by sorry
