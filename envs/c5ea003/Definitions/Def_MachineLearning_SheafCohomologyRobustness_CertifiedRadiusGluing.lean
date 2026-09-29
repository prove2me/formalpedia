-- Prove2me | Definitions.Def_MachineLearning_SheafCohomologyRobustness_CertifiedRadiusGluing
-- name    : MachineLearning_SheafCohomologyRobustness_CertifiedRadiusGluing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:58:02.901748+00:00
-- url     : https://prove2.me/theorems/4b0b13bc-49b4-4f83-b1d1-5fae29f3104f
-- title:
--   Aether Catalog definitions — MachineLearning_SheafCohomologyRobustness_CertifiedRadiusGluing
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.SheafCohomologyRobustness.CertifiedRadiusGluing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/SheafCohomologyRobustness/CertifiedRadiusGluing.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# From Sheaf Gluing to Certified `L∞` Radii, and Back

This file closes the loop of the research programme: it connects the purely
cohomological statements of `GraphNervePoincare` and `CyclicHolonomy` to genuine
analytic statements about a score function on input space, i.e. to *certified
adversarial robustness*.

The setting is a score function `s : E → ℝ` on a real normed space (for
`E = Fin d → ℝ` the norm is the `L∞` norm, see `linf_certified_of_coords`), a
family of anchor points `x : ι → E` indexed by the regions of a cover, and the
nerve graph `A` recording which regions overlap.

The **local sections** are the certified sign data `SignCertified s (x i) ρ (σ i)`:
on the closed `ρ`-ball around the anchor `x i`, the classifier's decision is
constantly `σ i`.  These are exactly the local sections of the (locally constant)
"decision sheaf" on the cover.

Main results.

* `sign_eq_of_overlap` — local sections agree on overlaps: certified regions
  whose anchors are within the certified radius carry the same sign.  This is
  the sheaf compatibility condition, and it is *forced* by certification.
* `sign_const_along_walk`, `glued_sign_constant` — hence on a connected nerve the
  local sections glue to a single global section: `H⁰` of the decision sheaf is
  one-dimensional (the sign is a global constant).
* `glued_global_certificate` — the glued section is a genuine global certificate:
  every point within `ρ` of *any* anchor receives the same decision.  Vanishing
  obstruction ⟹ certified `L∞` radius `ρ` on the entire union of regions.
* `exists_sign_flip_edge`, `exists_boundary_point_near` — conversely, a walk with
  nonzero sign holonomy contains an overlap across which the decision flips, and
  the intermediate value theorem then produces an **explicit boundary point**
  within distance `δ` of an anchor.
* `not_certified_of_holonomy` — therefore a nonzero sign holonomy *caps* the
  certified radius: some region cannot be certified beyond the overlap scale
  `δ`.  This is the sharp converse: cohomological obstruction ⟹ adversarial
  vulnerability at an explicitly bounded scale.
* `certified_radius_iff_no_sign_holonomy` — the two directions combined: on a
  connected nerve with overlap scale `δ`, uniform certification at radius `δ`
  is **equivalent** to the vanishing of the sign holonomy of the decision sheaf.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): "certified `L∞` radius ≥ overlap scale" and
  "vanishing decision-sheaf holonomy" are not merely related, they are
  *equivalent* on a connected nerve.  Bold form: certification is a cohomological
  property, not an analytic one.
* Experiment (Experimenter): the forward direction is a sheaf-gluing induction
  along walks (`sign_const_along_walk`); the converse needs the IVT applied to
  the segment joining the two anchors of the flipping overlap
  (`exists_boundary_point_near`), which is why continuity of the score — and
  nothing else, no Lipschitz bound — is the exact hypothesis.
* Analysis (Analyst): a first attempt phrased the obstruction with `ℝ`-valued
  margins; that failed to be an obstruction at all, since every margin
  discrepancy on a *tree* is a coboundary.  The right coefficient object is the
  **sign** (a `±1`-valued, i.e. `ℤ/2`-like, local section), whose holonomy is a
  genuine invariant. "Needed a different definition", not "false".
* Critique (Critic): `not_certified_of_holonomy` is nonvacuous — its hypotheses
  are satisfiable (any continuous score changing sign along a chain of nearby
  anchors), and its conclusion is a strict negation of a certification claim,
  witnessed by an explicit boundary point.
* Synthesis (PI): the equivalence `certified_radius_iff_no_sign_holonomy` is the
  formal version of the programme's slogan "vanishing first cohomology on the
  nerve certifies an `L∞` perturbation radius".
-/


open Set

namespace SheafCohomologyRobustness
namespace CertifiedGluing

open GraphNerve

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E]

/-! ## §1. Local sections of the decision sheaf -/

/-- `SignCertified s x ρ σ` : the score `s` has constant sign `σ` (with `σ = ±1`)
on the closed ball of radius `ρ` around `x`.  This is a local section of the
decision sheaf over the region, i.e. a local robustness certificate. -/
def SignCertified (s : E → ℝ) (x : E) (ρ : ℝ) (σ : ℝ) : Prop :=
  ∀ y, ‖y - x‖ ≤ ρ → 0 < σ * s y



/-! ## §2. Gluing: `H⁰` of the decision sheaf on a connected nerve -/

variable {A : ι → ι → Prop} {s : E → ℝ} {x : ι → E} {σ : ι → ℝ} {ρ : ℝ}





/-! ## §3. The converse: sign holonomy caps the certified radius -/





/-! ## §4. The equivalence -/




end CertifiedGluing
end SheafCohomologyRobustness


