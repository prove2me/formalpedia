-- Prove2me | Theorems.Thm_TropicalSocialChoice_distortedRule_not_isTropLinear
-- name    : TropicalSocialChoice.distortedRule_not_isTropLinear
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:16:06.623441+00:00
-- url     : https://prove2.me/theorems/ca3d68a1-52c1-4dd6-ba55-d3054d1b103e
-- title:
--   The rule is not tropically linear.
-- statement:
--   **The rule is not tropically linear.**  Its coefficients would have to be
--   `a₀ = a₁ = 1`, i.e. the Rawlsian rule, which disagrees with it on `testProfile`.
--
--   ```lean
--   theorem TropicalSocialChoice.distortedRule_not_isTropLinear: ¬ IsTropLinear distortedRule := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceNonlinear.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceNonlinear.lean#L160

-- Thm stub generated from Probability/TropicalSocialChoiceNonlinear.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceNonlinear
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice IV: linearity cannot be dropped from the oligarchy theorem

`Probability.TropicalSocialChoiceOligarchy` proved the *tropical oligarchy theorem*: a
**tropically linear**, unanimous, diagonally idempotent rule `f : TRⁿ → TR` is the minimum
rule `x ↦ ⨁_{i ∈ s} xᵢ` of a nonempty coalition `s`.  Conjecture 1 of
`FUTURE_DIRECTIONS.md` asked whether the linearity hypothesis is redundant, as it is for
the full multiplicativity axiom (`isTropLinear_of_tropIIA`).

**It is not.**  This file constructs an explicit counterexample and thereby refutes
Conjecture 1.

The counterexample is the two-voter rule
`f (x₀, x₁) = x₀ ⊕ φ(x₁) = min (x₀, φ(x₁))`,
where `φ` is the piecewise-linear cost distortion `φ(r) = 2r` for `r ≥ 0` and `φ(r) = r/2`
for `r < 0` (and `φ(∞) = ∞`).  The point is that `φ` is monotone (hence `⊕`-additive) and
*doubling-homogeneous*, `φ(2r) = 2φ(r)`, but not a translation `r ↦ a + r`.  Diagonal
idempotence only ever tests `f` along the doubling map, so it cannot see the difference,
whereas full multiplicativity would.

## Main results

* `phiT_add`, `phiT_mul_self`, `phiT_ge` : the distortion `φ` preserves tropical addition,
  is homogeneous along the diagonal, and is a *penalty* (`c ≤ φ c`).
* `distortedRule_tropIIA`, `distortedRule_tropPareto`, `distortedRule_tropDiagIdem` : the
  rule satisfies tropical IIA, tropical Pareto and diagonal idempotence.
* `distortedRule_not_isTropLinear` : it is **not** tropically linear.
* `distortedRule_ne_tropCoalition` : it differs from every coalition rule.
* `not_oligarchy_of_tropIIA_tropDiagIdem` : the refutation of Conjecture 1 — there is a
  rule satisfying `TropIIA`, `TropPareto` and `TropDiagIdem` which is not a coalition rule
  (and not even tropically linear).  Hence the oligarchy theorem genuinely needs its
  linearity hypothesis, in sharp contrast with the tropical Arrow theorem.
-/

open TropicalSocialChoice

open Tropical

/-! ## A monotone, doubling-homogeneous cost distortion which is not a translation -/














/-! ## The counterexample rule -/

theorem TropicalSocialChoice.distortedRule_not_isTropLinear: ¬ IsTropLinear distortedRule := by sorry
