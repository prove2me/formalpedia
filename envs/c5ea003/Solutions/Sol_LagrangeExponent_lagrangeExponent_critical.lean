-- Prove2me | solution 1 for LagrangeExponent.lagrangeExponent_critical
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:30:52.879355+00:00
-- url     : https://prove2.me/submissions/5c10ee71-6f29-4f57-8acf-d0da279e85a2

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




/-- The critical value: the cubic's unique inflection/critical point `y = 1/3` sits at mass
`1/27`. -/
@[simp] lemma lagrangeCubic_third : lagrangeCubic (1 / 3 : ℝ) = 1 / 27 := by
  unfold lagrangeCubic; norm_num







/-! ## Sample values (sanity checks on the normalisation) -/







open LagrangeExponent in
@[simp] theorem solution: lagrangeExponent (1 / 27 : ℝ) = 1 / 3 := by
  calc lagrangeExponent (1 / 27 : ℝ)
      = lagrangeExponent (lagrangeCubic (1 / 3)) := by rw [lagrangeCubic_third]
    _ = 1 / 3 := lagrangeExponent_lagrangeCubic _
