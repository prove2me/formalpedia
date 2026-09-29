-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
-- name    : Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:18:15.55396+00:00
-- url     : https://prove2.me/theorems/ca201bfc-206f-4f11-8c63-14bc981538e3
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.ThreeIsogenyMontgomery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/ThreeIsogenyMontgomery.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
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

namespace Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## The three-division polynomial and the Costello–Hisil formulas -/

/-- The three-division polynomial of the Montgomery curve `E_A`; its roots are
the abscissae of the points of order three. -/
def threeDivPoly (A r : K) : K := 3 * r ^ 4 + 4 * A * r ^ 3 + 6 * r ^ 2 - 1

/-- The Montgomery parameter of the quotient of `E_A` by the order-three point
with abscissa `r`. -/
def threeIsoParam (A r : K) : K := (A * r - 6 * r ^ 2 + 6) * r

/-- The twist coefficient of the target model of the 3-isogeny. -/
def threeIsoTwist (r : K) : K := r ^ 2

/-- The explicit 3-isogeny of Montgomery curves. -/
def threeIsoMap (r : K) (P : K × K) : K × K :=
  (P.1 * (P.1 * r - 1) ^ 2 / (P.1 - r) ^ 2,
    P.2 * (P.1 * r - 1) * (P.1 ^ 2 * r - 3 * P.1 * r ^ 2 + P.1 + r) / (P.1 - r) ^ 3)



/-! ## Uniformisation by the kernel abscissa -/

/-- The source parameter of the one-parameter family. -/
def mont3Source (r : K) : K := (1 - 6 * r ^ 2 - 3 * r ^ 4) / (4 * r ^ 3)

/-- The target parameter of the one-parameter family. -/
def mont3Target (r : K) : K := (1 + 18 * r ^ 2 - 27 * r ^ 4) / (4 * r)




/-! ## Discriminant factors -/



/-! ## The `j`-invariants of the family -/

/-- Numerator polynomial of the source `j`-invariant. -/
def threeNumP (r : K) : K := 9 * r ^ 8 - 12 * r ^ 6 + 30 * r ^ 4 - 12 * r ^ 2 + 1

/-- Numerator polynomial of the target `j`-invariant. -/
def threeNumQ (r : K) : K := 729 * r ^ 8 - 972 * r ^ 6 + 270 * r ^ 4 - 12 * r ^ 2 + 1

/-- The source `j`-invariant as a rational function of the kernel abscissa. -/
def jSource3 (r : K) : K := threeNumP r ^ 3 / (r ^ 12 * (r ^ 2 - 1) ^ 3 * (9 * r ^ 2 - 1))

/-- The target `j`-invariant as a rational function of the kernel abscissa. -/
def jTarget3 (r : K) : K := threeNumQ r ^ 3 / (r ^ 4 * (9 * r ^ 2 - 1) ^ 3 * (r ^ 2 - 1))



/-! ## The level-three modular polynomial -/

/-- The classical modular polynomial of level three. -/
def modPoly3 (X Y : K) : K :=
  X ^ 4 + Y ^ 4 - X ^ 3 * Y ^ 3 + 2232 * (X ^ 3 * Y ^ 2 + X ^ 2 * Y ^ 3)
    - 1069956 * (X ^ 3 * Y + X * Y ^ 3) + 36864000 * (X ^ 3 + Y ^ 3)
    + 2587918086 * (X ^ 2 * Y ^ 2) + 8900222976000 * (X ^ 2 * Y + X * Y ^ 2)
    + 452984832000000 * (X ^ 2 + Y ^ 2) - 770845966336000000 * (X * Y)
    + 1855425871872000000000 * (X + Y)





/-! ## The dual isogeny as an involution of the parameter -/



/-! ## The 3-isogeny graph is at most 4-regular -/

/-- `Φ₃(j, ·)` as an honest univariate polynomial. -/
noncomputable def modPoly3Y (j : K) : K[X] :=
  C 1 * X ^ 4 + C (-(j ^ 3) + 2232 * j ^ 2 - 1069956 * j + 36864000) * X ^ 3
    + C (2232 * j ^ 3 + 2587918086 * j ^ 2 + 8900222976000 * j + 452984832000000) * X ^ 2
    + C (-1069956 * j ^ 3 + 8900222976000 * j ^ 2 - 770845966336000000 * j
        + 1855425871872000000000) * X
    + C (j ^ 4 + 36864000 * j ^ 3 + 452984832000000 * j ^ 2
        + 1855425871872000000000 * j)





end Cryptography.IsogenySIDH


