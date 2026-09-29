-- Prove2me | Theorems.Thm_Cryptography_IsogenySIDH_modPoly3_three_isogeny
-- name    : Cryptography.IsogenySIDH.modPoly3_three_isogeny
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:43:19.88515+00:00
-- url     : https://prove2.me/theorems/e0d49217-1e0f-4fa4-8671-3f259292949c
-- title:
--   The `Φ₃` certificate for the Montgomery 3-isogeny.
-- statement:
--   **The `Φ₃` certificate for the Montgomery 3-isogeny.**  If `r` is the
--   abscissa of a point of order three on `E_A` and the two degenerate loci
--   `r² = 1`, `9r² = 1` are avoided, then the `j`-invariant of `E_A` and the
--   `j`-invariant of the Costello–Hisil target are a zero of the level-three modular
--   polynomial.  This is the level-3 analogue of `modPoly2_radical_step`.
--
--   ```lean
--   theorem Cryptography.IsogenySIDH.modPoly3_three_isogeny{A r : K} (htwo : (2 : K) ≠ 0)
--       (hpsi : threeDivPoly A r = 0) (h1 : r ^ 2 - 1 ≠ 0) (h9 : 9 * r ^ 2 - 1 ≠ 0) :
--       modPoly3 (jMont A) (jMont (threeIsoParam A r)) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/ThreeIsogenyMontgomery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/ThreeIsogenyMontgomery.lean#L225

-- Thm stub generated from Cryptography/IsogenySIDH/ThreeIsogenyMontgomery.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
/-
# Level three: the 3-isogeny of a Montgomery curve and its `Φ₃` certificate

The previous cycle's Conjecture 1 asked for the level-`ℓ` analogue of the
`Φ₂`-certificate proved in `ModularTwoIsogeny`: an explicit Montgomery-side
`ℓ`-isogeny formula together with a proof that the source and target
`j`-invariants are a zero of the classical modular polynomial `Φ_ℓ`.  This file
delivers the case `ℓ = 3`, which is the case used by SIDH/SIKE-style protocols
on the "3-side" of the isogeny graph.

Set-up: `E_A : y² = x³ + A x² + x` has a point of order three with abscissa `r`
exactly when `r` is a root of the three-division polynomial

  `threeDivPoly A r = 3r⁴ + 4A r³ + 6r² - 1`.

Then (Costello–Hisil) the quotient by that point is the Montgomery curve with
parameter `threeIsoParam A r = (A r - 6r² + 6) r`, and the quotient map is

  `(x,y) ↦ ( x (xr-1)²/(x-r)² , y (xr-1)(x²r - 3xr² + x + r)/(x-r)³ )`.

Results:

* `threeDivPoly_root_ne_zero` — a root of the three-division polynomial is
  automatically nonzero, so the formulas never divide by zero at `r`.
* `threeIso_mem` — **correctness of the explicit 3-isogeny**: the map above
  sends affine points of `E_A` (away from the kernel abscissa `r`) to the
  generalized Montgomery curve `r² Y² = X³ + A' X² + X`; the twist coefficient
  is exactly `r²`.  This is the level-3 analogue of `radTwoIso_mem`.
* `three_param_eq`, `three_target_eq` — the whole configuration is uniformised
  by `r`: `A = (1 - 6r² - 3r⁴)/(4r³)` and `A' = (1 + 18r² - 27r⁴)/(4r)`, so both
  curves are points of a one-parameter family.  This is what makes the modular
  identity a *univariate* rational identity.
* `mont3Source_disc`, `mont3Target_disc` — the two discriminant factors are
  `A² - 4 = (r²-1)³(9r²-1)/(16r⁶)` and `A'² - 4 = (9r²-1)³(r²-1)/(16r²)`; the
  striking exchange of exponents `3 ↔ 1` between source and target is the
  fingerprint of the degree-3 isogeny.
* `modPoly3_three_isogeny` — **the `Φ₃` certificate**: `Φ₃(j(E_A), j(E_{A'})) = 0`.
* `three_isogeny_dual_involution` — `r ↦ 1/(3r)` exchanges source and target up
  to sign, i.e. it realises the dual isogeny on the uniformising parameter.
* `three_isogeny_neighbours_card_le_four` — `Φ₃` is monic of degree four in each
  variable, so the 3-isogeny graph is at most 4-regular.
-/

set_option maxHeartbeats 2000000

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## The three-division polynomial and the Costello–Hisil formulas -/







/-! ## Uniformisation by the kernel abscissa -/






/-! ## Discriminant factors -/



/-! ## The `j`-invariants of the family -/







/-! ## The level-three modular polynomial -/

theorem Cryptography.IsogenySIDH.modPoly3_three_isogeny{A r : K} (htwo : (2 : K) ≠ 0)
    (hpsi : threeDivPoly A r = 0) (h1 : r ^ 2 - 1 ≠ 0) (h9 : 9 * r ^ 2 - 1 ≠ 0) :
    modPoly3 (jMont A) (jMont (threeIsoParam A r)) = 0 := by sorry
