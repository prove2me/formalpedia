-- Prove2me | solution 1 for Cryptography.IsogenySIDH.threeIso_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:54:04.972284+00:00
-- url     : https://prove2.me/submissions/6c0f8367-1033-48bd-9a84-156cc6dac548

-- Sol generated from Cryptography/IsogenySIDH/ThreeIsogenyMontgomery.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_MontgomeryModelFibres
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
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





/-- A root of the three-division polynomial is never zero. -/
theorem threeDivPoly_root_ne_zero {A r : K} (h : threeDivPoly A r = 0) : r ≠ 0 := by
  intro hr
  rw [hr] at h
  simp only [threeDivPoly] at h
  norm_num at h


/-! ## Uniformisation by the kernel abscissa -/






/-! ## Discriminant factors -/



/-! ## The `j`-invariants of the family -/







/-! ## The level-three modular polynomial -/






/-! ## The dual isogeny as an involution of the parameter -/



/-! ## The 3-isogeny graph is at most 4-regular -/







open Cryptography.IsogenySIDH in
theorem solution{A r x y : K} (htwo : (2 : K) ≠ 0)
    (hpsi : threeDivPoly A r = 0) (hxr : x - r ≠ 0) (hP : OnMontgomery A (x, y)) :
    genMont (threeIsoTwist r) (threeIsoParam A r) (threeIsoMap r (x, y)) := by
  have hr : r ≠ 0 := threeDivPoly_root_ne_zero hpsi
  have hP' : y ^ 2 = x ^ 3 + A * x ^ 2 + x := hP
  have hpsi' : 3 * r ^ 4 + 4 * A * r ^ 3 + 6 * r ^ 2 - 1 = 0 := hpsi
  have hfour : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]; exact mul_ne_zero htwo htwo
  have h4r3 : (4 : K) * r ^ 3 ≠ 0 := mul_ne_zero hfour (pow_ne_zero 3 hr)
  have hA : A = (1 - 6 * r ^ 2 - 3 * r ^ 4) / (4 * r ^ 3) := by
    rw [eq_div_iff h4r3]
    linear_combination hpsi'
  subst hA
  simp only [genMont, threeIsoTwist, threeIsoParam, threeIsoMap]
  have h2 : (y * (x * r - 1) * (x ^ 2 * r - 3 * x * r ^ 2 + x + r) / (x - r) ^ 3) ^ 2
      = y ^ 2 * ((x * r - 1) * (x ^ 2 * r - 3 * x * r ^ 2 + x + r) / (x - r) ^ 3) ^ 2 := by
    ring
  rw [h2, hP']
  field_simp
  ring
