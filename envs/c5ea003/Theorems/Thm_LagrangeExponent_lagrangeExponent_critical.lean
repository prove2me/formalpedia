-- Prove2me | Theorems.Thm_LagrangeExponent_lagrangeExponent_critical
-- name    : LagrangeExponent.lagrangeExponent_critical
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:06:10.921856+00:00
-- url     : https://prove2.me/theorems/715c11d8-9dd7-48b0-bd45-a2c6e9541744
-- title:
--   At the critical mass `1/27` the exponent is exactly the degenerate critical point `1/3`.
-- statement:
--   At the critical mass `1/27` the exponent is exactly the degenerate critical point `1/3`.
--
--   ```lean
--   theorem LagrangeExponent.lagrangeExponent_critical: lagrangeExponent (1 / 27 : ℝ) = 1 / 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LagrangeExponentCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LagrangeExponentCore.lean#L159

-- Thm stub generated from Novelty/LagrangeExponentCore.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
/-
# The Lagrange Exponent `σ`: signed cube roots and the critical cubic

This file sets up the object studied in `Novelty.LagrangeExponentConcavity`.

## The model

Fix a three–slot branching mechanism whose *growth rate* `y` is tied to the total
mass `t` through the **critical cubic**

  `lagrangeCubic y = y ^ 3 - y ^ 2 + y / 3 = t`.

This is the unique (up to affine normalisation) monic cubic whose derivative is a
perfect square, `h' y = 3 (y - 1/3) ^ 2 ≥ 0`: the three roots of the resolvent
coalesce at the single critical point `y = 1/3`.  Consequently `h` is a strictly
monotone bijection of `ℝ`, and Lagrange's resolvent method degenerates to a single
real radical:

  `lagrangeCubic y = ((3 y - 1) ^ 3 + 1) / 27`,

so its inverse — the **Lagrange exponent** — is

  `σ t = (1 + ∛(27 t - 1)) / 3`.

The critical value `h (1/3) = 1/27` is therefore *canonically* attached to the
mechanism, not chosen by hand; it is exactly the mass at which the growth rate
passes the degenerate critical point.  It is also, by AM–GM, the largest possible
product of a three–point mass distribution (see `Novelty.LagrangeExponentConcavity`).

## Contents

* `cbrt` — the odd (sign–aware) real cube root, with `cbrt_cube`, `cbrt_strictMono`.
* `lagrangeCubic`, `lagrangeCubic_eq_shift`, `lagrangeCubic_strictMono`.
* `lagrangeExponent`, and the two inversion theorems
  `lagrangeExponent_lagrangeCubic` / `lagrangeCubic_lagrangeExponent`,
  giving `σ = h⁻¹` as an order isomorphism of `ℝ`.
-/

open LagrangeExponent

open Set

/-! ## The odd real cube root -/













/-! ## The critical cubic and its inverse -/











/-! ## Sample values (sanity checks on the normalisation) -/


@[simp]

theorem LagrangeExponent.lagrangeExponent_critical: lagrangeExponent (1 / 27 : ℝ) = 1 / 3 := by sorry
