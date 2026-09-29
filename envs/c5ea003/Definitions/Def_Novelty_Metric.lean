-- Prove2me | Definitions.Def_Novelty_Metric
-- name    : Novelty_Metric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:47.497307+00:00
-- url     : https://prove2.me/theorems/538d4738-9450-42c0-95c0-3e7c7181586a
-- title:
--   Aether Catalog definitions — Novelty_Metric
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Metric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Metric.lean by skeleton subtraction
import Mathlib

/-!
# Split geometry on `ℝ²` — the manifold and the metric tensor

This file sets up the *split geometry* studied in this development.  The underlying
manifold is `M := ℝ × ℝ` with its standard smooth structure.  On it we place the
Riemannian metric
$$ g \;=\; \frac{dx \otimes dx}{\cosh^2 y} \;+\; \cosh^2 x \; dy \otimes dy , $$
i.e. the metric whose component matrix in the global coordinates `(x, y)` is the
diagonal matrix `diag (sech²  y, cosh²  x)`.

We record:

* `SplitGeometry.M` — the manifold, a smooth manifold via the standard instance for a
  finite dimensional real normed space;
* `SplitGeometry.Emet`, `SplitGeometry.Gmet` — the two metric coefficients
  `E(p) = sech²(y)` and `G(p) = cosh²(x)`;
* `SplitGeometry.gForm` — the metric as a bilinear form on tangent vectors
  (tangent vectors to `ℝ²` are again elements of `ℝ²`);
* positivity of the coefficients, symmetry and **positive definiteness** of `g`;
* **smoothness** of the coefficients (`ContDiff ℝ ⊤`), hence smoothness of `g`.

All statements here are true as literally stated for the metric in the problem.
-/

namespace SplitGeometry

open Real

/-- The manifold `M := ℝ × ℝ` with global coordinates `(x, y) = (p.1, p.2)`. -/
abbrev M : Type := ℝ × ℝ

open scoped Manifold in
/-- Coefficient `E(p) = sech²(y) = 1 / cosh²(y)` of `dx ⊗ dx`. -/
noncomputable def Emet (p : M) : ℝ := (Real.cosh p.2)⁻¹ ^ 2

/-- Coefficient `G(p) = cosh²(x)` of `dy ⊗ dy`. -/
noncomputable def Gmet (p : M) : ℝ := (Real.cosh p.1) ^ 2

/-- The Riemannian metric `g` as a bilinear form on tangent vectors `v, w ∈ ℝ²`:
`g_p(v, w) = E(p) · v₁ w₁ + G(p) · v₂ w₂`. -/
noncomputable def gForm (p : M) (v w : M) : ℝ :=
  Emet p * (v.1 * w.1) + Gmet p * (v.2 * w.2)







/-
**Positive definiteness**: `g_p(v, v) = 0` iff `v = 0`.
-/

/-
**Positive definiteness** (strict form): a nonzero tangent vector has positive
length squared.
-/

/-
The coefficient `E = sech²` is a smooth function on `M`.
-/

/-
The coefficient `G = cosh²` is a smooth function on `M`.
-/

/-
**Smoothness of the metric**: for fixed tangent vectors `v, w`, the map
`p ↦ g_p(v, w)` is smooth.
-/

end SplitGeometry


