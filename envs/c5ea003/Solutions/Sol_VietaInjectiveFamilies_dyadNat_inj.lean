-- Prove2me | solution 1 for VietaInjectiveFamilies.dyadNat_inj
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:34:01.224953+00:00
-- url     : https://prove2.me/submissions/cbf56a7b-2c10-4389-ac02-a53e3e089c04

-- Sol generated from NumberTheory/VietaInjectiveFamilies.lean
import Mathlib
import Definitions.Def_NumberTheory_VietaInjectiveFamilies
import Theorems.Thm_VietaInjectiveFamilies_dyadNat_factorization_two

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

/-- For a fixed positive `a`, the map `b ↦ 3ab(a+b)` is strictly monotone. -/
theorem vieta_strictMono_snd {a : ℕ} (ha : 1 ≤ a) :
    StrictMono (fun b : ℕ => 3 * a * b * (a + b)) := by
  intro b c hbc
  have hlt : b * (a + b) < c * (a + c) := by nlinarith
  have h3a : 0 < 3 * a := by omega
  calc 3 * a * b * (a + b) = (3 * a) * (b * (a + b)) := by ring
    _ < (3 * a) * (c * (a + c)) := by exact Nat.mul_lt_mul_of_pos_left hlt h3a
    _ = 3 * a * c * (a + c) := by ring


/-! ## The represented set and its cardinality -/






/-! ## The spine `a = 1` -/







/-! ## Both signs at once -/




/-! ## The dyadic two-parameter family `a = 2^i`, `b` odd -/







open VietaInjectiveFamilies in
theorem solution{i j b c : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hb : Odd b) (hc : Odd c) (hb0 : 0 < b) (hc0 : 0 < c)
    (h : dyadNat i b = dyadNat j c) : i = j ∧ b = c := by
  have hij : i = j := by
    have h1 := dyadNat_factorization_two hi hb hb0
    have h2 := dyadNat_factorization_two hj hc hc0
    rw [h] at h1
    omega
  subst hij
  refine ⟨rfl, ?_⟩
  have hpow : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have := (vieta_strictMono_snd (a := 2 ^ i) hpow).injective (a₁ := b) (a₂ := c)
  apply this
  simpa [dyadNat] using h
