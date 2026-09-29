-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
-- name    : ErdosProblems_Erdos1041_Counterexample_Bottleneck
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:59:55.676865+00:00
-- url     : https://prove2.me/theorems/23d97054-fa77-4552-b1f3-f62e90a03d50
-- title:
--   Slit-domain and quadratic bottleneck coordinates
-- statement:
--   Defines the slit domain, projection, quotient, quadratic coordinate, and near-critical region used in the bottleneck estimate for paths and connected sets. Covering and lower-bound properties are separate theorems with their stated hypotheses.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Bottleneck.lean#L1-L1585
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of Lemma 2.3 and Corollary 2.4 from `ani_degree7_counterexample.tex`. -/

/-!
This module owns slice S3 and declares `s3_bottleneck_length` at the interface
name and statement, with no `sorry`.

The proof isolates two topological hypotheses.  The covering hypothesis is
`s3_bottleneck_isCoveringMap`.  The
connectedness hypothesis is replaced by the sharper
`bottleneck_slit_preimage_near`: the holomorphic square root of `𝒜/â` supplies
the paper's quadratic coordinate `ψ`, its two branches `ψ = ±η` give two
preimages of each slit point next to `cc`, `hzeros` makes the covering
two-sheeted, and a third preimage anywhere in the component would produce a
third preimage of a nearby point of the slit disc.  So every slit preimage in
the component is one of the two local branches, hence inside the disk-criterion
radius.  Neither Rouché's theorem nor the argument principle is used; see
`bottleneck_ball_subset_image` and `bottleneck_sublevel_isPreconnected`.
-/

noncomputable section

open Topology

namespace Erdos1041.Counterexample

/-! ### Two `ℝ`-on-`ℂ` scalar-action instances

`StarConvex ℝ (0 : ℂ)` elaborates its `SMul ℝ ℂ` to `Algebra.toSMul` (through
`NormedAlgebra ℝ ℂ`), and for that particular instance path Mathlib v4.29.1 does
not resolve `ContinuousSMul ℝ ℂ` or `NormSMulClass ℝ ℂ` by typeclass search.
Both are true and are proved here from `Complex.real_smul`, which rewrites the
action to multiplication by the real coercion.  They are `private`: nothing
outside this file needs them. -/

private instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    have hfun : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [hfun]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

private instance instNormSMulClassRealComplex : NormSMulClass ℝ ℂ where
  norm_smul r z := by
    rw [show r • z = (r : ℂ) * z from Complex.real_smul, norm_mul]
    simp

/-- The displacement parametrisation of the paper's radial slit. -/
def bottleneckSlit (v : ℂ) : Set ℂ :=
  {w | ∃ t : ℝ, 0 ≤ t ∧ t < 1 - ‖v‖ ∧
    w = v + (t : ℂ) * (v / (‖v‖ : ℂ))}



































/-- The slit disc, as a subtype suitable for covering-space lifting. -/
def bottleneckSlitBase (v : ℂ) : Set ℂ :=
  {w | ‖w‖ < 1 ∧ w ∉ bottleneckSlit v}











/-- The component with the slit preimage removed. -/
def bottleneckSlitDomain (p : Polynomial ℂ) (cc : ℂ) : Set ℂ :=
  {z | z ∈ connectedComponentIn (Omega p) cc ∧
    p.eval z ∉ bottleneckSlit (p.eval cc)}

/-- The polynomial restriction used for L2. -/
def bottleneckSlitProjection (p : Polynomial ℂ) (cc : ℂ) :
    bottleneckSlitDomain p cc → bottleneckSlitBase (p.eval cc) :=
  fun z => ⟨p.eval z, ⟨connectedComponentIn_subset (Omega p) cc z.2.1, z.2.2⟩⟩













section Probe
end Probe

/-! ## Two complex-analysis tools

Mathlib v4.29.1 has neither Rouché's theorem nor the argument principle, and
`DiffContOnCl.ball_subset_image_closedBall` loses a factor of two that the
constants of Corollary 2.4 cannot afford.  Both tools are proved here instead
from the open mapping theorem and the maximum modulus principle. -/





/-! ## The quadratic coordinate `ψ` of Corollary 2.4

The paper's inverse quadratic coordinate `χ` is built from the holomorphic
square root of `𝒜(z)/â`, which exists because the disk criterion `hdisk` puts
that quotient in `closedBall 1 (1/4)`, well inside `Complex.slitPlane`. -/

/-- The normalised quadratic factor `𝒜(z)/â`. -/
def bottleneckQuot (p : Polynomial ℂ) (cc aHat z : ℂ) : ℂ :=
  (shiftQuad p cc).eval z / aHat

/-- The paper's quadratic coordinate `ψ(z) = z √(𝒜(z)/â)`.  It satisfies
`p (cc + z) - p cc = â ψ(z)²`, and on the disk-criterion radius it is comparable
to `z`, so it separates the two branches of `p` at the critical point. -/
def bottleneckPsi (p : Polynomial ℂ) (cc aHat z : ℂ) : ℂ :=
  z * Complex.sqrt (bottleneckQuot p cc aHat z)

/-- The open set on which `ψ` is holomorphic. -/
def bottleneckPsiDomain (p : Polynomial ℂ) (cc aHat : ℂ) : Set ℂ :=
  bottleneckQuot p cc aHat ⁻¹' Complex.slitPlane

























/-! ## The two local preimages lie in the distinguished component

Both preimages produced by `bottleneck_two_preimages` sit inside the sublevel
set `‖ψ‖ < s`, on which `‖p - p cc‖ = ‖â‖ ‖ψ‖² < δ`, so that sublevel set lies
inside the lemniscate.  It is preconnected by the minimum-modulus tool, and it
contains `0`; so its translate by `cc` is a preconnected subset of `Ω(p)`
through `cc`, hence inside the component. -/

/-- The sublevel set of `‖ψ‖` that joins the two local preimages to `cc`. -/
def bottleneckNear (p : Polynomial ℂ) (cc aHat : ℂ) (h s : ℝ) : Set ℂ :=
  {z | z ∈ Metric.ball (0 : ℂ) h ∧ ‖bottleneckPsi p cc aHat z‖ < s}





/-! ## The covering hypothesis, discharged

`hcover` in `bottleneck_length_of_covering_and_preconnected` is the statement
that `p` restricted to the slit complement inside the distinguished component is
a covering map over the slit disc.  `PROOF.md` §2 gives the argument: the
restriction is proper (a polynomial is a proper map, the component is relatively
closed in the lemniscate) and a local homeomorphism (`huniq` puts the only
critical point at `cc`, whose value `p cc` is removed with the slit), and a
proper local homeomorphism out of a Hausdorff space is a covering map, which is
slice S2's `s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph`. -/

/-- The slit-complement domain sits inside the preimage of the slit disc. -/
theorem bottleneckSlitDomain_subset (p : Polynomial ℂ) (cc : ℂ) :
    bottleneckSlitDomain p cc ⊆
      (fun z => p.eval z) ⁻¹' bottleneckSlitBase (p.eval cc) := by
  rintro z ⟨hU, hJ⟩
  exact ⟨connectedComponentIn_subset (Omega p) cc hU, hJ⟩













/-! ## The fibres over the slit have at most two points

`hzeros` pins the fibre of the covering over `0` to `{b₁, b₂}`, so the covering
over the simply connected slit disc has exactly two sheets: the sections through
`b₁` and through `b₂`.  Points of the slit itself are limits of the slit disc,
so a third preimage there would produce a third preimage of a nearby point of
the slit disc through its inverse chart. -/













/-! ## Lemma 2.3 and Corollary 2.4

Both topological inputs of the conditional reduction are now discharged: the
covering by `s3_bottleneck_isCoveringMap`, and the localisation of the slit
preimage by `bottleneck_slit_preimage_near`, which replaces preconnectedness of
the whole slit preimage by the sharper statement that the two branches at `cc`
already exhaust each slit fibre. -/



end Erdos1041.Counterexample


