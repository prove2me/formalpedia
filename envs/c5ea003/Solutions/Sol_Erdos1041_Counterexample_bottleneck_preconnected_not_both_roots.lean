-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_preconnected_not_both_roots
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:38:16.040985+00:00
-- url     : https://prove2.me/submissions/12bcff48-3fb6-4c72-9032-4d2c495bca77

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_HausdorffLength
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_locPathConnected
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_simplyConnected
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_covering_fibre_eq_on_preconnected
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026. -/

/-!
# Erdős #1041 with length as one-dimensional Hausdorff measure

Formal Conjectures states Erdős #1041 with the length of a path defined as the
one-dimensional Hausdorff measure `μH[1]` of its image. `erdos1041_counterexample`
bounds the total variation of a parametrisation instead. This module proves the
Hausdorff form for the same polynomial `f`, and in a stronger shape: every
preconnected subset of the strict lemniscate `Ω(f)` that contains two distinct
roots has one-dimensional Hausdorff measure greater than two
(`erdos1041_counterexample_hausdorff`). The image of any path joining two roots
is such a set.

The argument reuses the bottleneck geometry of `Bottleneck.lean` and adds no
arc-extraction, rectifiability or length-of-arc lemma. Removing the slit
preimage from the component of `Ω(f)` through the critical point leaves an open
set in which no preconnected subset contains both roots, because the polynomial
restricted there is a covering of a simply connected base. So a preconnected
set `K` through both roots must, for every radius between the slit preimage and
a root, meet the circle of that radius about the critical point inside the
connected component of that root (`bottleneck_sheet_crossing`). The two
components are disjoint open sets, the distance to the critical point is
1-Lipschitz, and on the real line `μH[1]` is Lebesgue measure, so `μH[1] K` is at
least the sum of the two radial lengths (`s3_bottleneck_hausdorff`). That is the
same bound `s3_bottleneck_length` gives for total variation, so the numerical
margin of `Assembly.lean` applies unchanged.

`erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false` state the
Formal Conjectures parent `Erdos1041.erdos_1041` in its own vocabulary, with
`fcLength` its `length`, and refute it.

The mathematics of the counterexample is ani's. The polynomial is the single
member `s = 10⁻⁶` of ani's family fixed in `Defs.lean`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Polynomial Metric

namespace Erdos1041.Counterexample
/-! ## The slit domain separates the two roots -/
end Erdos1041.Counterexample

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ)
    (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (S : Set ℂ) (hS : IsPreconnected S) (hSD : S ⊆ bottleneckSlitDomain p cc)
    (hb₁ : b₁ ∈ S) (hb₂ : b₂ ∈ S) : False := by
  letI : SimplyConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_simplyConnected (p.eval cc) hv
  letI : LocPathConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_locPathConnected (p.eval cc) hv
  letI : PreconnectedSpace S := Subtype.preconnectedSpace hS
  let g : S → bottleneckSlitDomain p cc := fun x => ⟨x.1, hSD x.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hbase : bottleneckSlitProjection p cc (g ⟨b₁, hb₁⟩) =
      bottleneckSlitProjection p cc (g ⟨b₂, hb₂⟩) := by
    apply Subtype.ext
    change p.eval b₁ = p.eval b₂
    exact (show p.eval b₁ = 0 from hr₁).trans (show p.eval b₂ = 0 from hr₂).symm
  have heq := bottleneck_covering_fibre_eq_on_preconnected
    (bottleneckSlitProjection p cc) hcover Set.univ isPreconnected_univ
    g hg.continuousOn ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ (Set.mem_univ _) (Set.mem_univ _) hbase
  exact hne (congrArg Subtype.val heq)
