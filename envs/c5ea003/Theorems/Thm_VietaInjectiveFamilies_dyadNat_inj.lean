-- Prove2me | Theorems.Thm_VietaInjectiveFamilies_dyadNat_inj
-- name    : VietaInjectiveFamilies.dyadNat_inj
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:52:53.551174+00:00
-- url     : https://prove2.me/theorems/c4c2c65b-8748-4847-b25d-600716b8f7c9
-- title:
--   Injectivity of the dyadic family.
-- statement:
--   **Injectivity of the dyadic family.**  For `i ≥ 1` and odd positive `b`,
--   the pair `(i, b)` is recovered from the value `3 · 2^i · b · (2^i + b)`:
--   the exponent from the `2`-adic valuation, then `b` by monotonicity.
--
--   ```lean
--   theorem VietaInjectiveFamilies.dyadNat_inj{i j b c : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
--       (hb : Odd b) (hc : Odd c) (hb0 : 0 < b) (hc0 : 0 < c)
--       (h : dyadNat i b = dyadNat j c) : i = j ∧ b = c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/VietaInjectiveFamilies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/VietaInjectiveFamilies.lean#L371

-- Thm stub generated from NumberTheory/VietaInjectiveFamilies.lean
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

theorem VietaInjectiveFamilies.dyadNat_inj{i j b c : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hb : Odd b) (hc : Odd c) (hb0 : 0 < b) (hc0 : 0 < c)
    (h : dyadNat i b = dyadNat j c) : i = j ∧ b = c := by sorry
