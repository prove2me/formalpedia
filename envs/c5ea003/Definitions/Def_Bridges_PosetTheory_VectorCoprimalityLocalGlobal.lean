-- Prove2me | Definitions.Def_Bridges_PosetTheory_VectorCoprimalityLocalGlobal
-- name    : Bridges_PosetTheory_VectorCoprimalityLocalGlobal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:05.191599+00:00
-- url     : https://prove2.me/theorems/2970b42f-56a0-4e06-9f56-2b6c62facf15
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_VectorCoprimalityLocalGlobal
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.VectorCoprimalityLocalGlobal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/VectorCoprimalityLocalGlobal.lean by skeleton subtraction
import Mathlib

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

namespace VectorCoprimalityLocalGlobal

/-! ## Definitions -/

/-- The gcd of all coordinates of an integer vector `w : Fin k → ℤ`.  Because `Finset.gcd` over `ℤ`
returns the normalized (non-negative) gcd, `vecGcd` is always non-negative and `vecGcd 0 = 0`. -/
def vecGcd {k : ℕ} (w : Fin k → ℤ) : ℤ := Finset.univ.gcd w

/-- Coordinatewise reduction of an integer vector modulo `p`. -/
def redMod (p : ℕ) {k : ℕ} (w : Fin k → ℤ) : Fin k → ZMod p := fun i => (w i : ZMod p)

/-! ## Basic properties of `vecGcd` -/



/-! ## Theorem 1 -/


/-! ## Theorem 2 -/




/-! ## Theorem 3 — the local-global bridge -/


/-! ## Theorem 4

The brief's proposed multiplicativity `localDensity (p*q) S = localDensity p S * localDensity q S`
is false.  We record the brief's definitions and disprove the claim, then state and prove the
correct multiplicative density. -/

/-- The image of a finite set of integer vectors under reduction modulo `p` (brief's definition). -/
def redModFinset (p : ℕ) {k : ℕ} (S : Finset (Fin k → ℤ)) : Finset (Fin k → ZMod p) :=
  S.image (redMod p)

/-- The brief's "local density": `1 - |redMod p '' S| / p^k` (retained for the record; note the
multiplicativity claimed for it in the brief is false, see `localDensity_mul_counterexample`). -/
def localDensity (p : ℕ) {k : ℕ} (S : Finset (Fin k → ℤ)) : ℚ :=
  1 - (redModFinset p S).card / (p : ℚ) ^ k

/-- The explicit two-point counterexample set `{0, 1} ⊆ (Fin 1 → ℤ)`. -/
def counterSet : Finset (Fin 1 → ℤ) := {(fun _ => 0), (fun _ => 1)}



/-! ### Corrected Theorem 4: multiplicativity of the primitive-residue density -/

/-- A vector `x : Fin k → R` over a commutative ring `R` is *primitive* if its coordinates generate
the unit ideal, i.e. there is a linear combination of the coordinates equal to `1`.  This condition
is representation independent and, over a field `ZMod p`, is equivalent to `x` being non-zero. -/
def IsPrim {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) : Prop :=
  ∃ a : Fin k → R, ∑ i, a i * x i = 1



/-- The density of primitive residue vectors in `(ZMod n) ^ k`. -/
noncomputable def primDensity (n k : ℕ) : ℚ :=
  (Nat.card {x : Fin k → ZMod n // IsPrim x} : ℚ) / (n : ℚ) ^ k



end VectorCoprimalityLocalGlobal


