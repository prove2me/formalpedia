-- Prove2me | Theorems.Thm_VectorCoprimalityLocalGlobal_vecGcd_eq_one_iff
-- name    : VectorCoprimalityLocalGlobal.vecGcd_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:28:10.814682+00:00
-- url     : https://prove2.me/theorems/687431ae-122a-4ede-83a4-77971542f733
-- title:
--   Theorem 3 (main result).
-- statement:
--   **Theorem 3 (main result).** An integer vector is coprime (its coordinate gcd is `1`) iff for
--   every prime `p` its reduction modulo `p` is non-zero.  Coprimality is thus a local, per-prime
--   condition.
--
--   ```lean
--   theorem VectorCoprimalityLocalGlobal.vecGcd_eq_one_iff{k : ℕ} (w : Fin k → ℤ) :
--       vecGcd w = 1 ↔ ∀ p : ℕ, p.Prime → redMod p w ≠ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/VectorCoprimalityLocalGlobal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/VectorCoprimalityLocalGlobal.lean#L99

-- Thm stub generated from Bridges/PosetTheory/VectorCoprimalityLocalGlobal.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_VectorCoprimalityLocalGlobal

/-!
# Local-Global Bridge for Integer Vector Coprimality

This file formalizes the statement that **coprimality of an integer vector is a local
(per-prime) condition**, the foundational fact behind the Euler-product factorization of the
autocorrelation of simultaneously visible lattice points.

## Main definitions

* `VectorCoprimalityLocalGlobal.vecGcd w` : the (non-negative) gcd of all coordinates of an
  integer vector `w : Fin k → ℤ`.
* `VectorCoprimalityLocalGlobal.redMod p w` : the coordinatewise reduction of `w` modulo `p`.
* `VectorCoprimalityLocalGlobal.IsPrim x` : the coordinates of `x : Fin k → R` generate the unit
  ideal of the commutative ring `R` (a representation-independent primitivity condition).
* `VectorCoprimalityLocalGlobal.primDensity n k` : the density of primitive residue vectors in
  `(ZMod n) ^ k`.

## Main results

* `dvd_vecGcd_iff` (Theorem 1): `d ∣ vecGcd w ↔ ∀ i, d ∣ w i`.
* `redMod_eq_iff` (Theorem 2): `redMod p v = redMod p x ↔ (p : ℤ) ∣ vecGcd (v - x)`.
* `vecGcd_eq_one_iff` (Theorem 3, **the local-global bridge**):
  `vecGcd w = 1 ↔ ∀ p : ℕ, p.Prime → redMod p w ≠ 0`.
* `primDensity_mul` (corrected Theorem 4): for coprime `p q`,
  `primDensity (p*q) k = primDensity p k * primDensity q k`.

## Note on Theorem 4 of the research brief

The research brief proposed a "Theorem 4" of the form
`localDensity (p*q) S = localDensity p S * localDensity q S`, where
`localDensity p S = 1 - |redMod p '' S| / p^k`.  **This statement is false**: see
`localDensity_mul_counterexample` below, which exhibits `p = 2`, `q = 3`, `k = 1` and a two-point
set `S` for which the image cardinalities are all `2`, giving
`localDensity 6 S = 2/3 ≠ 0 = localDensity 2 S * localDensity 3 S`.
The image of a *fixed* finite set of integer vectors under reduction is not a CRT "product/cylinder"
set, so its cardinality is not multiplicative.

The multiplicativity that genuinely underlies the Euler product is the multiplicativity of the
**density of primitive residue vectors** (a Jordan-totient style quantity), captured here by
`primDensity_mul`.  The brief's definitions `redModFinset` and `localDensity` are retained (with the
counterexample proven) so that the record is complete.
-/

open Finset

open VectorCoprimalityLocalGlobal

/-! ## Definitions -/



/-! ## Basic properties of `vecGcd` -/



/-! ## Theorem 1 -/


/-! ## Theorem 2 -/




/-! ## Theorem 3 — the local-global bridge -/

theorem VectorCoprimalityLocalGlobal.vecGcd_eq_one_iff{k : ℕ} (w : Fin k → ℤ) :
    vecGcd w = 1 ↔ ∀ p : ℕ, p.Prime → redMod p w ≠ 0 := by sorry
