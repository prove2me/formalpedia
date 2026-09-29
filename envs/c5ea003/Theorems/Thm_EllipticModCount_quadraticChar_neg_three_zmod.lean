-- Prove2me | Theorems.Thm_EllipticModCount_quadraticChar_neg_three_zmod
-- name    : EllipticModCount.quadraticChar_neg_three_zmod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:13:32.270499+00:00
-- url     : https://prove2.me/theorems/b459e5eb-e7b6-47e7-89bc-df2d6a6f0f4d
-- title:
--   Supplementary quadratic reciprocity for `-3`, obtained from point counting.
-- statement:
--   **Supplementary quadratic reciprocity for `-3`, obtained from point counting.**
--   `-3` is a nonsquare mod `p` exactly when `p ≡ 2 (mod 3)`.
--
--   ```lean
--   theorem EllipticModCount.quadraticChar_neg_three_zmod(hp2 : p ≠ 2) (hp3 : p ≠ 3) :
--       quadraticChar (ZMod p) (-3) = -1 ↔ p % 3 = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticModP.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticModP.lean#L150

-- Thm stub generated from Combinatorics/EllipticModP.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticVerticalMoment
/-
# Modular invariants of point counts over the prime fields `ZMod p`

This file specialises the general finite-field results of
`Combinatorics.EllipticPointCount` to the prime fields `F_p = ZMod p`, producing
*exact* point counts and divisibility ("modular") invariants that depend only on
the residue class of `p`.

Main results:

* `EllipticModCount.cardPoints_zmod_eq_of_three` : if `p % 3 = 2` then
  `y^2 = x^3 + b` has exactly `p + 1` points, so `a_p = 0` and `3 ∣ #E(F_p)`.
* `EllipticModCount.cardPoints_zmod_eq_of_four` : if `p % 4 = 3` then
  `y^2 = x^3 + a*x` has exactly `p + 1` points, so `a_p = 0` and `4 ∣ #E(F_p)`.
* `EllipticModCount.two_dvd_cardPoints_zmod_iff` : the 2-torsion parity criterion
  over `F_p`.
* `EllipticModCount.hasse_of_supersingular_three` / `..._four` : the two
  supersingular families satisfy the Hasse bound with equality `a_p = 0`.
-/

open EllipticModCount

open Finset

variable {p : ℕ} [Fact p.Prime]

theorem EllipticModCount.quadraticChar_neg_three_zmod(hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    quadraticChar (ZMod p) (-3) = -1 ↔ p % 3 = 2 := by sorry
