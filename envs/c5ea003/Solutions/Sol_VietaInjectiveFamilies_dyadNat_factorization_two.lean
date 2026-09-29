-- Prove2me | solution 1 for VietaInjectiveFamilies.dyadNat_factorization_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:31:06.335063+00:00
-- url     : https://prove2.me/submissions/1e86ff11-f19d-4d13-a5f1-c82a0aed980f

-- Sol generated from NumberTheory/VietaInjectiveFamilies.lean
import Mathlib
import Definitions.Def_NumberTheory_VietaInjectiveFamilies

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

open VietaInjectiveFamilies

/-! ## Basic definitions -/







/-! ## The symmetry group: why global injectivity is impossible -/









/-! ## Multiplicity of a Vieta value is bounded by its divisor count -/



/-! ## The represented set and its cardinality -/






/-! ## The spine `a = 1` -/







/-! ## Both signs at once -/




/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/







open VietaInjectiveFamilies in
theorem solution{i b : ℕ} (hi : 1 ≤ i) (hb : Odd b) (hb0 : 0 < b) :
    (dyadNat i b).factorization 2 = i := by
  have hpow : Even (2 ^ i) := by
    refine (Nat.even_pow).mpr ⟨even_two, by omega⟩
  have hoddsum : Odd (2 ^ i + b) := hpow.add_odd hb
  have hodd : Odd (3 * b * (2 ^ i + b)) := ((odd_two_mul_add_one 1).mul hb).mul hoddsum
  have hfac : dyadNat i b = 2 ^ i * (3 * b * (2 ^ i + b)) := by unfold dyadNat; ring
  have hne : (3 * b * (2 ^ i + b)) ≠ 0 := by
    have : 0 < 3 * b * (2 ^ i + b) := by positivity
    omega
  have hpne : (2 : ℕ) ^ i ≠ 0 := by positivity
  rw [hfac, Nat.factorization_mul hpne hne]
  have h1 : ((2 : ℕ) ^ i).factorization 2 = i := by
    rw [Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have h2 : (3 * b * (2 ^ i + b)).factorization 2 = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    have hmod := Nat.odd_iff.mp hodd
    omega
  rw [Finsupp.add_apply, h1, h2, Nat.add_zero]
