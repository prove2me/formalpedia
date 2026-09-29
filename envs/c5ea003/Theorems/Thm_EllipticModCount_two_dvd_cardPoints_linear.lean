-- Prove2me | Theorems.Thm_EllipticModCount_two_dvd_cardPoints_linear
-- name    : EllipticModCount.two_dvd_cardPoints_linear
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:13:55.110535+00:00
-- url     : https://prove2.me/theorems/8ec8ec01-248b-4c4d-8eb4-9b99b6483d8f
-- title:
--   On the family `y^2 = x^3 + a*x` with `a ≠ 0` the point `(0,0)` is `2`-torsion, and
-- statement:
--   On the family `y^2 = x^3 + a*x` with `a ≠ 0` the point `(0,0)` is `2`-torsion, and
--   indeed the point count is even; for `p % 4 = 3` this is consistent with the exact count
--   `p + 1`.
--
--   ```lean
--   theorem EllipticModCount.two_dvd_cardPoints_linear(hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
--       2 ∣ cardPoints a (0 : ZMod p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EllipticModP.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EllipticModP.lean#L120

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

theorem EllipticModCount.two_dvd_cardPoints_linear(hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    2 ∣ cardPoints a (0 : ZMod p) := by sorry
