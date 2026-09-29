-- Prove2me | Definitions.Def_Bridges_NeuralCoding_EMLUniversalApproximation
-- name    : Bridges_NeuralCoding_EMLUniversalApproximation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:13.61923+00:00
-- url     : https://prove2.me/theorems/cce50f3e-3ab7-49ce-b050-6b63be7451c4
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_EMLUniversalApproximation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.EMLUniversalApproximation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/EMLUniversalApproximation.lean by skeleton subtraction
import Mathlib

/-! # EML Universal Approximation via Stone-Weierstrass

This file records the precise Stone–Weierstrass consequence available for EML
expressions.  The generated algebra consists of finite algebraic combinations of
an injective EML feature.  It is dense on a compact domain.

An earlier draft stated that a *single* function `a * exp (b*x)` approximates every
continuous function.  That assertion is false (a nonzero such function has constant
sign), so the original declaration is retained below in a comment and replaced by
the generated-algebra statement.  The draft also asserted the substantially stronger
single-hidden-layer logistic universal approximation theorem without developing its
required analytic machinery.  It too is retained in a comment, followed by the exact
Stone–Weierstrass formulation proved here.
-/

noncomputable section

open Real

namespace EMLUniversalApproximation

open scoped unitInterval


/-- The continuous exponential feature on the unit interval. -/
def unitIntervalExp : C(unitInterval, ℝ) where
  toFun x := Real.exp (x : ℝ)
  continuous_toFun := Real.continuous_exp.comp continuous_subtype_val



/-
The original (false) draft was:

```
theorem eml_approximates_continuous_on_unit_interval
    (f : C(unitInterval, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : unitInterval → ℝ,
      (∃ a b : ℝ, g = fun x => a * exp (b * (x : ℝ))) ∧
      ∀ x : unitInterval, |g x - f x| < ε
```

A single scaled exponential cannot approximate, for example, a continuous function
which is uniformly positive at one point and uniformly negative at another.
-/



/-
The previous `exp_separates_points_real` used the impossible premise
`∀ t, f t = exp (f t)` and did not assume that `f` itself separates `x` and `y`.
Its conclusion was therefore only vacuously true.  The actual separation theorem is
`EMLStoneWeierstrassBridge.exp_separates` (or `unitIntervalExp_adjoin_separates`).
-/


/-
The original draft also gave, with no supporting development, the stronger theorem
that every continuous function on `[0,1]` is approximated by a finite *linear sum* of
logistic ridge functions.  Stone–Weierstrass for the generated algebra does not by
itself identify every algebra element with that restricted one-layer architecture,
so that declaration is not silently claimed here.
-/


end EMLUniversalApproximation


