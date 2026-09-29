-- Prove2me | Definitions.Def_Novelty_Geodesic
-- name    : Novelty_Geodesic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:21.921968+00:00
-- url     : https://prove2.me/theorems/e254f310-f759-4661-a14f-f35b864d5110
-- title:
--   Aether Catalog definitions — Novelty_Geodesic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Geodesic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Geodesic.lean by skeleton subtraction
import Mathlib

/-!
# Geodesic equations of the split geometry and the coordinate-axis geodesics

For the metric `g = sech²(y) dx² + cosh²(x) dy²` on `M = ℝ²` the (nonzero) Christoffel
symbols in the coordinates `(x, y)` are

* `Γ¹₁₂ = Γ¹₂₁ = -tanh y`
* `Γ¹₂₂ = -cosh x · sinh x · cosh² y`
* `Γ²₁₁ = sech² y · tanh y / cosh² x`
* `Γ²₁₂ = Γ²₂₁ = tanh x`

(`Γ¹₁₁ = Γ²₂₂ = 0`).  These are obtained from
`Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢ gⱼˡ + ∂ⱼ gᵢˡ - ∂ˡ gᵢⱼ)` with the diagonal metric
`g₁₁ = sech² y`, `g₂₂ = cosh² x`, `g₁₂ = 0` and inverse `g¹¹ = cosh² y`,
`g²² = sech² x`.

A curve `t ↦ (x t, y t)` is a **geodesic** iff it satisfies the two second-order ODEs
`ẍ + Γ¹ᵢⱼ u̇ⁱ u̇ʲ = 0` and `ÿ + Γ²ᵢⱼ u̇ⁱ u̇ʲ = 0`.

## Corrected solutions

The problem statement proposed the curves `x = x₀ + a t, y = y₀ eᵗ` (x-direction) and
`y = y₀ + b t, x = x₀ e⁻ᵗ` (y-direction).  These do **not** solve the geodesic
equations of this metric (see `claimed_x_curve_not_geodesic`).  The genuine geodesics
tangent to the coordinate axes are the coordinate straight lines:

* along the x-axis: `t ↦ (x₀ + a t, 0)` (`xAxis_geodesic`);
* along the y-axis: `t ↦ (0, y₀ + b t)` (`yAxis_geodesic`).

The exponential factors `e^{±t}` predicted in the problem describe not the geodesics
themselves but the **geodesic deviation** (Jacobi fields), studied in `Deviation.lean`.
-/

namespace SplitGeometry

open Real

/-- Christoffel symbol `Γ¹₁₂ = Γ¹₂₁ = -tanh y` (argument order `(x, y)`). -/
noncomputable def Chr1_12 (_a b : ℝ) : ℝ := - Real.tanh b

/-- Christoffel symbol `Γ¹₂₂ = -cosh x · sinh x · cosh² y`. -/
noncomputable def Chr1_22 (a b : ℝ) : ℝ := - Real.cosh a * Real.sinh a * (Real.cosh b) ^ 2

/-- Christoffel symbol `Γ²₁₁ = sech² y · tanh y / cosh² x`. -/
noncomputable def Chr2_11 (a b : ℝ) : ℝ := (Real.cosh b)⁻¹ ^ 2 * Real.tanh b / (Real.cosh a) ^ 2

/-- Christoffel symbol `Γ²₁₂ = Γ²₂₁ = tanh x`. -/
noncomputable def Chr2_12 (a _b : ℝ) : ℝ := Real.tanh a

/-- The geodesic equations for a coordinate curve `t ↦ (x t, y t)`.  We use that
`Γ¹₁₁ = Γ²₂₂ = 0`, so the `ẋ²` term is absent in the first equation and the `ẏ²`
term is absent in the second. -/
def IsGeodesic (x y : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv x) t
        + 2 * Chr1_12 (x t) (y t) * deriv x t * deriv y t
        + Chr1_22 (x t) (y t) * (deriv y t) ^ 2 = 0)
  ∧ (∀ t, deriv (deriv y) t
        + Chr2_11 (x t) (y t) * (deriv x t) ^ 2
        + 2 * Chr2_12 (x t) (y t) * deriv x t * deriv y t = 0)

/-
**X-axis geodesic.**  The coordinate straight line `t ↦ (x₀ + a t, 0)` tangent to
the x-axis is a geodesic of the split metric.
-/

/-
**Y-axis geodesic.**  The coordinate straight line `t ↦ (0, y₀ + b t)` tangent to
the y-axis is a geodesic of the split metric.
-/

/-
**The proposed exponential curve is not a geodesic.**  The curve
`x t = t, y t = eᵗ` from the (incorrect) problem statement violates the first geodesic
equation at `t = 0`, where the left-hand side equals `-2 tanh 1 ≠ 0`.
-/

end SplitGeometry


