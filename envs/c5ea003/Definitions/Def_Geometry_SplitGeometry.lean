-- Prove2me | Definitions.Def_Geometry_SplitGeometry
-- name    : Geometry_SplitGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:47.71058+00:00
-- url     : https://prove2.me/theorems/fc0c1f1b-d175-4995-ba13-dbfdcc04f2d8
-- title:
--   Aether Catalog definitions — Geometry_SplitGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SplitGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SplitGeometry.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Split Geometry: a transcendental–algebraic bridge for a direction-dependent metric

We study the *Split Geometry* on `ℝ²` with the diagonal Riemannian metric
`ds² = dx²/cosh²y + cosh²x · dy²`, which expands in the `x`-direction and
contracts in the `y`-direction.  Attached to it is the **phase function**

  `K x y = sech²x − sech²y`,     where `sech t = 1 / cosh t`,

whose sign was proposed as the sign of the curvature and which is supposed to
determine an "elliptic" region, a "hyperbolic" region, and a flat
"phase boundary".

## The connector theorem (analysis ↔ algebraic geometry)

The first group of results forms a bridge between two a-priori unrelated areas:

* the **transcendental analysis** of the hyperbolic secant `sech = 1/cosh`, and
* the **plane algebraic geometry** of the degenerate conic `x² = y²`
  (the union of the two diagonal lines `y = x` and `y = -x`).

Concretely we prove that the entire sign structure of the transcendental
function `K x y = sech²x − sech²y` is governed *exactly* by the algebraic
comparison of `x²` and `y²`:

* `splitPhase_eq_zero_iff` :  `K x y = 0 ↔ x² = y²`
* `splitPhase_pos_iff`     :  `0 < K x y ↔ x² < y²`
* `splitPhase_neg_iff`     :  `K x y < 0 ↔ y² < x²`

and, translating the algebraic variety `x² = y²` into its two irreducible
linear components, the phase boundary is exactly the pair of diagonals:

* `splitPhase_boundary`    :  `K x y = 0 ↔ (y = x ∨ y = -x)`.

We also record that the metric is genuinely Riemannian (its coefficient
functions are everywhere positive, so the metric is positive definite), and the
"split duality" `K x y = -K y x` that interchanges the two phases.

## Christoffel symbols

The second group of results carries out the Levi-Civita computation the prompt
asks for.  For the diagonal metric `g_xx = sech²y`, `g_yy = cosh²x` we compute
the two nonzero metric derivatives (`∂_y g_xx`, `∂_x g_yy`) rigorously with
`HasDerivAt`, define the six Christoffel symbols by the standard diagonal-metric
formulas, and prove their closed forms:

* `Gamma_xxy_eq` : `Γ¹₁₂ = -tanh y`
* `Gamma_yxy_eq` : `Γ²₁₂ = tanh x`
* `Gamma_xyy_eq` : `Γ¹₂₂ = -cosh x · sinh x · cosh²y`
* `Gamma_yxx_eq` : `Γ²₁₁ = sinh y / (cosh³y · cosh²x)`
* `Gamma_xxx_deriv_zero`, `Gamma_yyy_deriv_zero` : the two vanishing components.

## A note on the conjectured curvature

The research prompt conjectured that the *Gaussian* curvature of the metric is
exactly `K x y = sech²x − sech²y`.  A direct Brioschi computation shows this is
only correct *on the coordinate axes*; off the axes the true Gaussian curvature
is `-cosh²y + (2·sech²y − 1)·sech²x`, which is not the clean diagonal expression
(see `ComputationalEvidence.md`).  We therefore state the theorems about the
proposed sign field `K` on its own terms — as an exact transcendental/algebraic
identity of independent interest — rather than asserting it equals the curvature.
The sign field `K` does agree with the true curvature *in sign* along the axes,
where the "expanding/contracting" intuition of the geometry is cleanest.
-/

open Real

namespace SplitGeometry

/-- `sechSq t = 1 / cosh² t`, the square of the hyperbolic secant. -/
noncomputable def sechSq (t : ℝ) : ℝ := 1 / Real.cosh t ^ 2

/-- The first metric coefficient `g_xx = 1/cosh²y = sech²y` of the split metric
`ds² = dx²/cosh²y + cosh²x·dy²`. -/
noncomputable def gxx (_x y : ℝ) : ℝ := sechSq y

/-- The second metric coefficient `g_yy = cosh²x` of the split metric. -/
noncomputable def gyy (x _y : ℝ) : ℝ := Real.cosh x ^ 2

/-- The **phase function** `K x y = sech²x − sech²y`.  Its sign is the object of
the connector theorem: it is governed exactly by the algebraic sign of
`x² − y²`. -/
noncomputable def splitPhase (x y : ℝ) : ℝ := sechSq x - sechSq y

/-! ## The metric is a genuine Riemannian metric -/





/-! ## The connector theorem: analysis ↔ algebraic geometry -/











/-! ## Christoffel symbols of the split metric -/




/-- `Γ¹₁₂ = Γ¹₂₁ = (∂_y g_xx)/(2 g_xx)`. -/
noncomputable def Gamma_xxy (x y : ℝ) : ℝ := (deriv (fun y' => gxx x y') y) / (2 * gxx x y)

/-- `Γ¹₂₂ = -(∂_x g_yy)/(2 g_xx)`. -/
noncomputable def Gamma_xyy (x y : ℝ) : ℝ := - (deriv (fun x' => gyy x' y) x) / (2 * gxx x y)

/-- `Γ²₁₁ = -(∂_y g_xx)/(2 g_yy)`. -/
noncomputable def Gamma_yxx (x y : ℝ) : ℝ := - (deriv (fun y' => gxx x y') y) / (2 * gyy x y)

/-- `Γ²₁₂ = Γ²₂₁ = (∂_x g_yy)/(2 g_yy)`. -/
noncomputable def Gamma_yxy (x y : ℝ) : ℝ := (deriv (fun x' => gyy x' y) x) / (2 * gyy x y)







end SplitGeometry


