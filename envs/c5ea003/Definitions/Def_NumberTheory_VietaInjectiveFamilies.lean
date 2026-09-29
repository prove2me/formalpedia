-- Prove2me | Definitions.Def_NumberTheory_VietaInjectiveFamilies
-- name    : NumberTheory_VietaInjectiveFamilies
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:21.106106+00:00
-- url     : https://prove2.me/theorems/d3881c88-869c-4f46-954c-4488abbab562
-- title:
--   Aether Catalog definitions — NumberTheory_VietaInjectiveFamilies
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.VietaInjectiveFamilies`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/VietaInjectiveFamilies.lean by skeleton subtraction
import Mathlib

/-!
# Injective subfamilies of the Vieta three-cube identity

The Vieta identity `a³ + b³ + (-a-b)³ = -3ab(a+b)` produces, for every pair of
integers `(a, b)`, an integer which is a sum of three cubes.  This file studies
the *value map* `vietaValue a b = -3ab(a+b)` of that identity from the point of
view of injectivity and of quantitative counting:

* the exact six-element symmetry group of the value map (`vietaValue_symm_*`),
  which is the structural reason why the map is never injective on all of `ℤ²`;
* a residual collision *inside* the fundamental domain `1 ≤ a ≤ b`
  (`vieta_not_injOn_fundamental_domain`), showing that no ordering restriction
  alone can produce injectivity;
* a divisor bound for the multiplicity of a value
  (`vieta_multiplicity_le_card_divisors`), which is the arithmetic mechanism
  behind those collisions;
* two genuinely injective subfamilies:
  the *spine* `a = 1` (`spineNat_strictMono`) and the two-parameter
  *dyadic family* `a = 2^i`, `b` odd (`dyadNat_inj`), whose injectivity is
  proved via the `2`-adic valuation;
* quantitative lower bounds for the number of positive integers `≤ N` produced
  by the identity, all of them with **three nonzero cubes** (no padded `0³`):
  `vieta_count_ge_sqrt` gives `⌊√(N/6)⌋` and `vieta_count_dyadic` gives a
  two-parameter count `I * m`.

Everything is elementary but the counting statements are honest cardinality
statements about `Set.ncard` of the represented sets.
-/

namespace VietaInjectiveFamilies

/-! ## Basic definitions -/

/-- `k` is a sum of three **nonzero** integral cubes: no padded zero cube. -/
def SumOfThreeNonzeroCubes (k : ℤ) : Prop :=
  ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 3 + y ^ 3 + z ^ 3 = k

/-- The value map of the Vieta identity. -/
def vietaValue (a b : ℤ) : ℤ := -3 * a * b * (a + b)


/-- `k` is *Vieta represented* if it arises from the identity with all three
cubes nonzero. -/
def VietaRepresented (k : ℤ) : Prop :=
  ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 ∧ vietaValue a b = k



/-! ## The symmetry group: why global injectivity is impossible -/









/-! ## Multiplicity of a Vieta value is bounded by its divisor count -/



/-! ## The represented set and its cardinality -/

/-- Positive integers up to `N` produced by the Vieta identity. -/
def repSet (N : ℕ) : Set ℤ :=
  {k | 0 < k ∧ k ≤ (N : ℤ) ∧ VietaRepresented k}





/-! ## The spine `a = 1` -/

/-- The spine of the Vieta family: `spineNat b = 3b(b+1) = -vietaValue 1 b`. -/
def spineNat (b : ℕ) : ℕ := 3 * b * (b + 1)






/-! ## Both signs at once -/

/-- Nonzero integers of absolute value at most `N` produced by the identity. -/
def absRepSet (N : ℕ) : Set ℤ :=
  {k | k ≠ 0 ∧ |k| ≤ (N : ℤ) ∧ VietaRepresented k}



/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/

/-- The dyadic Vieta family `dyadNat i b = 3 · 2^i · b · (2^i + b)`. -/
def dyadNat (i b : ℕ) : ℕ := 3 * 2 ^ i * b * (2 ^ i + b)





end VietaInjectiveFamilies


