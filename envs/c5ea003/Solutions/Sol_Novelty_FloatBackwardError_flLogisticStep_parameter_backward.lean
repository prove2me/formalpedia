-- Prove2me | solution 1 for Novelty.FloatBackwardError.flLogisticStep_parameter_backward
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:14:38.683372+00:00
-- url     : https://prove2.me/submissions/03c74ce3-7ae7-4d18-8053-43c3cbfd4b15

-- Sol generated from Novelty/FloatLogisticParameterError.lean
import Mathlib
import Definitions.Def_Novelty_FloatBackwardErrorHorner
import Definitions.Def_Novelty_FloatLogisticParameterError
import Definitions.Def_Novelty_FloatPseudoOrbitShadowing
import Theorems.Thm_Novelty_FloatBackwardError_gamma_mul_bound

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

open Novelty.FloatBackwardError




/-- Elementary bound: the product of three factors `1 + eᵢ` with `|eᵢ| ≤ u`
differs from `1` by at most `γ₃(u)`. -/
lemma abs_prod_three_sub_one {u e₁ e₂ e₃ : ℝ} (hu : 0 ≤ u)
    (h₁ : |e₁| ≤ u) (h₂ : |e₂| ≤ u) (h₃ : |e₃| ≤ u) :
    |(1 + e₁) * (1 + e₂) * (1 + e₃) - 1| ≤ gamma u 3 := by
  have hg1 : ∀ e : ℝ, |e| ≤ u → |(1 + e) - 1| ≤ gamma u 1 := by
    intro e he
    simpa [gamma] using he
  have h12 := gamma_mul_bound hu (hg1 e₁ h₁) (hg1 e₂ h₂)
  have h123 := gamma_mul_bound hu h12 (hg1 e₃ h₃)
  simpa using h123








open Novelty.FloatBackwardError in
theorem solution(M : RoundingModel) (r x : ℝ) :
    ∃ r' : ℝ, |r' - r| ≤ gamma M.u 3 * |r| ∧ flLogisticStep M r x = logisticMap r' x := by
  obtain ⟨e₁, he₁, hsub⟩ := M.sub_spec 1 x
  obtain ⟨e₂, he₂, hmul₂⟩ := M.mul_spec x (M.sub 1 x)
  obtain ⟨e₃, he₃, hmul₃⟩ := M.mul_spec r (M.mul x (M.sub 1 x))
  refine ⟨r * ((1 + e₁) * (1 + e₂) * (1 + e₃)), ?_, ?_⟩
  · have hkey : r * ((1 + e₁) * (1 + e₂) * (1 + e₃)) - r
        = ((1 + e₁) * (1 + e₂) * (1 + e₃) - 1) * r := by ring
    rw [hkey, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_prod_three_sub_one M.u_nonneg he₁ he₂ he₃) (abs_nonneg r)
  · rw [flLogisticStep, hmul₃, hmul₂, hsub, logisticMap]
    ring
