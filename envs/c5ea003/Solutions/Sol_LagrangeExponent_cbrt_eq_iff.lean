-- Prove2me | solution 1 for LagrangeExponent.cbrt_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:28:37.02802+00:00
-- url     : https://prove2.me/submissions/e55f97c0-f562-4297-b9d3-3df53de4fb86

-- Sol generated from Novelty/LagrangeExponentCore.lean
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







open LagrangeExponent in
theorem solution{x y : ℝ} : cbrt x = y ↔ y ^ 3 = x := by
  constructor
  · rintro rfl; exact cbrt_cube x
  · rintro rfl; exact cube_strictMono.injective (by simp)
