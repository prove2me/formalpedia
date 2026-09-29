-- Prove2me | Theorems.Thm_VietaInjectiveFamilies_vieta_multiplicity_le_card_divisors
-- name    : VietaInjectiveFamilies.vieta_multiplicity_le_card_divisors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:53:11.546467+00:00
-- url     : https://prove2.me/theorems/d209aa3a-d115-46dc-b754-4f097360e705
-- title:
--   Divisor bound for the multiplicity.
-- statement:
--   **Divisor bound for the multiplicity.**  The number of ordered pairs of
--   positive integers `(a,b)` with `3ab(a+b) = v` is at most the number of divisors
--   of `v`: the first coordinate divides `v` and determines the second.
--
--   ```lean
--   theorem VietaInjectiveFamilies.vieta_multiplicity_le_card_divisors(v : ℕ) (hv : v ≠ 0) :
--       (((Finset.Icc 1 v ×ˢ Finset.Icc 1 v).filter
--           (fun p => 3 * p.1 * p.2 * (p.1 + p.2) = v)).card) ≤ v.divisors.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/VietaInjectiveFamilies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/VietaInjectiveFamilies.lean#L135

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

theorem VietaInjectiveFamilies.vieta_multiplicity_le_card_divisors(v : ℕ) (hv : v ≠ 0) :
    (((Finset.Icc 1 v ×ˢ Finset.Icc 1 v).filter
        (fun p => 3 * p.1 * p.2 * (p.1 + p.2) = v)).card) ≤ v.divisors.card := by sorry
