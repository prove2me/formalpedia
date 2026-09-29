-- Prove2me | Definitions.Def_Novelty_LagrangeExponentCore
-- name    : Novelty_LagrangeExponentCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:26.011934+00:00
-- url     : https://prove2.me/theorems/96c2c568-708d-4025-a319-9de691d312d9
-- title:
--   Aether Catalog definitions — Novelty_LagrangeExponentCore
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.LagrangeExponentCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/LagrangeExponentCore.lean by skeleton subtraction
import Mathlib
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

namespace LagrangeExponent

open Set

/-! ## The odd real cube root -/

/-- The real (sign–aware) cube root: `cbrt x` is the unique real `y` with `y ^ 3 = x`. -/
noncomputable def cbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ ((1 : ℝ) / 3) else -((-x) ^ ((1 : ℝ) / 3))

lemma cbrt_of_nonneg {x : ℝ} (hx : 0 ≤ x) : cbrt x = x ^ ((1 : ℝ) / 3) := if_pos hx

lemma cbrt_of_neg {x : ℝ} (hx : x < 0) : cbrt x = -((-x) ^ ((1 : ℝ) / 3)) :=
  if_neg (not_le.2 hx)

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hx]
  norm_num

/-- Cubing is a strictly monotone bijection of `ℝ` (the odd–exponent power map). -/
lemma cube_strictMono : StrictMono fun a : ℝ => a ^ 3 := Odd.strictMono_pow (by decide)

/-- `cbrt` is a genuine cube root. -/
@[simp] lemma cbrt_cube (x : ℝ) : (cbrt x) ^ 3 = x := by
  by_cases hx : 0 ≤ x
  · rw [cbrt_of_nonneg hx, rpow_third_cube hx]
  · push_neg at hx
    rw [cbrt_of_neg hx]
    have h : (0 : ℝ) ≤ -x := by linarith
    have := rpow_third_cube h
    nlinarith [this]




/-- `cbrt` is strictly monotone (it inverts the strictly monotone map `y ↦ y ^ 3`). -/
lemma cbrt_strictMono : StrictMono cbrt := by
  intro a b hab
  by_contra hcon
  push_neg at hcon
  have h3 : (cbrt b) ^ 3 ≤ (cbrt a) ^ 3 := cube_strictMono.le_iff_le.2 hcon
  rw [cbrt_cube, cbrt_cube] at h3
  linarith



/-! ## The critical cubic and its inverse -/

/-- The critical cubic `h y = y³ - y² + y/3`, the unique monic cubic (normalised so that
`h 0 = 0`) whose derivative `3 (y - 1/3)²` is a perfect square. -/
noncomputable def lagrangeCubic (y : ℝ) : ℝ := y ^ 3 - y ^ 2 + y / 3

/-- Lagrange's resolvent for the degenerate cubic: `h` is an affine shift of a pure cube. -/
lemma lagrangeCubic_eq_shift (y : ℝ) : lagrangeCubic y = ((3 * y - 1) ^ 3 + 1) / 27 := by
  unfold lagrangeCubic; ring

lemma lagrangeCubic_strictMono : StrictMono lagrangeCubic := by
  intro a b hab
  rw [lagrangeCubic_eq_shift, lagrangeCubic_eq_shift]
  have h1 : 3 * a - 1 < 3 * b - 1 := by linarith
  have h2 : (3 * a - 1) ^ 3 < (3 * b - 1) ^ 3 := cube_strictMono h1
  linarith


/-- The **Lagrange exponent** `σ t = (1 + ∛(27 t - 1)) / 3`: the growth rate attached to
total mass `t`. -/
noncomputable def lagrangeExponent (t : ℝ) : ℝ := (1 + cbrt (27 * t - 1)) / 3

/-- `σ t` really is a root of the critical cubic. -/
@[simp] theorem lagrangeCubic_lagrangeExponent (t : ℝ) :
    lagrangeCubic (lagrangeExponent t) = t := by
  rw [lagrangeCubic_eq_shift, lagrangeExponent]
  have h : 3 * ((1 + cbrt (27 * t - 1)) / 3) - 1 = cbrt (27 * t - 1) := by ring
  rw [h, cbrt_cube]
  ring

/-- `σ` is the two–sided inverse of the critical cubic. -/
@[simp] theorem lagrangeExponent_lagrangeCubic (y : ℝ) :
    lagrangeExponent (lagrangeCubic y) = y :=
  lagrangeCubic_strictMono.injective (lagrangeCubic_lagrangeExponent _)


theorem lagrangeExponent_strictMono : StrictMono lagrangeExponent := by
  intro a b hab
  have : 27 * a - 1 < 27 * b - 1 := by linarith
  have := cbrt_strictMono this
  unfold lagrangeExponent
  linarith


/-! ## Sample values (sanity checks on the normalisation) -/






end LagrangeExponent


