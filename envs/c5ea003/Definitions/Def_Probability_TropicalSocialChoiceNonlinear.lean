-- Prove2me | Definitions.Def_Probability_TropicalSocialChoiceNonlinear
-- name    : Probability_TropicalSocialChoiceNonlinear
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:12.337202+00:00
-- url     : https://prove2.me/theorems/62d71a22-8620-43de-9c64-3924c4a8ae28
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoiceNonlinear
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoiceNonlinear`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoiceNonlinear.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
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

namespace TropicalSocialChoice

open Tropical

/-! ## A monotone, doubling-homogeneous cost distortion which is not a translation -/

/-- The real cost distortion `φ(r) = 2r` for `r ≥ 0`, `φ(r) = r/2` for `r < 0`. -/
noncomputable def phiR (r : ℝ) : ℝ := if 0 ≤ r then 2 * r else r / 2

/-- `φ` extended to extended costs, with `φ(∞) = ∞`. -/
noncomputable def phiT (c : TR) : TR := trop ((untrop c).map phiR)












/-! ## The counterexample rule -/

/-- The two-voter rule `f (x₀, x₁) = min (x₀, φ x₁)`: voter `1`'s costs are distorted
before being compared with voter `0`'s. -/
noncomputable def distortedRule : (Fin 2 → TR) → TR := fun x => x 0 + phiT (x 1)





/-- The test profile: voter `0` reports the infinitely bad cost `⊤`, voter `1` reports
the cost `1`. -/
noncomputable def testProfile : Fin 2 → TR := ![0, ofReal 1]








end TropicalSocialChoice


