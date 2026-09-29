-- Prove2me | Definitions.Def_Novelty_FloatLogisticParameterError
-- name    : Novelty_FloatLogisticParameterError
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:26:50.178652+00:00
-- url     : https://prove2.me/theorems/6911db18-8018-4d13-b248-5b4eb078f62a
-- title:
--   Aether Catalog definitions — Novelty_FloatLogisticParameterError
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FloatLogisticParameterError`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FloatLogisticParameterError.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing

/-!
# Structural backward error: a floating-point logistic map is an exact logistic map

Fourth cycle.  The backward-error statement of the first cycle
(`hornerFl_backward`) perturbs the coefficients of the polynomial *individually*,
so the perturbed system need not belong to the original parameterised family.
For the natural product implementation of the logistic map,

```
  fl_step r x  =  fl( r ⊗ fl( x ⊗ fl(1 ⊖ x) ) )
```

a much stronger, *structural* backward-error statement holds: the computed value
is the exact value of the logistic map **of the same family** at a perturbed
parameter `r'` with `|r' - r| ≤ γ₃(u) |r|`
(`flLogisticStep_parameter_backward`).  Consequently a floating-point logistic
execution is the exact orbit of a nonautonomous logistic family whose parameters
stay in a relative `γ₃(u)`-neighbourhood of `r`
(`flLogisticOrbit_exact_family`).

The boundary of the statement is also identified: the perturbed parameter may
exceed `4`, in which case `[0,1]` is no longer invariant
(`parameter_overshoot_escapes`), which is exactly why the runtime hypothesis
"the execution was observed to remain in `[0,1]`" cannot be dropped from
`logistic_binary64_shadowing`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): rounding errors in a *structured* evaluation scheme
should be expressible as perturbations *within* the model family, not merely as
arbitrary coefficient perturbations; if so, floating-point chaos experiments
simulate a genuine (slightly detuned) member of the family exactly.
Experiment (Experimenter): for the three-operation product form the three
relative errors combine into the single factor `(1+e₁)(1+e₂)(1+e₃)`, which
multiplies `r` alone.  The subtraction `1 ⊖ x` is the only step where structure
could fail, and it does not: its relative error again scales the whole product.
Analysis (Analyst): the same argument fails for Horner form
`r ⊗ (x ⊗ (1 ⊖ x))` versus the expanded form `r x - r x²`, where the two
monomials acquire *different* factors — structural backward error is a property
of the *program*, not of the mathematical function.  This is the sharpest
formulation of "backward-error semantics is a semantics of programs".
Critique (Critic): `|r' - r| ≤ γ₃|r|` allows `r' > 4`; the escape lemma shows
this is not vacuous, so the invariance hypothesis in the shadowing corollary is
load-bearing.
-- !-- End Lab Notes -- !--
-/

namespace Novelty.FloatBackwardError

/-- The logistic map with parameter `r`. -/
def logisticMap (r z : ℝ) : ℝ := r * (z * (1 - z))

/-- The natural floating-point implementation `fl(r ⊗ fl(x ⊗ fl(1 ⊖ x)))`. -/
def flLogisticStep (M : RoundingModel) (r x : ℝ) : ℝ :=
  M.mul r (M.mul x (M.sub 1 x))





/-- The floating-point logistic orbit. -/
def flLogisticOrbit (M : RoundingModel) (r x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => flLogisticStep M r (flLogisticOrbit M r x₀ n)




end Novelty.FloatBackwardError


