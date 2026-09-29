-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_sheet_crossing
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:48:15.484287+00:00
-- url     : https://prove2.me/submissions/2afa9a5e-3221-4e1f-9900-bd8cdb1989cc

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_HausdorffLength
import Theorems.Thm_Erdos1041_Counterexample_zero_not_mem_bottleneckSlit
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitDomain_isOpen
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_preconnected_not_both_roots
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

/-- A root in the distinguished component lies in the slit domain: its value
`0` is not on the slit of a nonzero critical value. -/
theorem bottleneck_root_mem_slitDomain (p : Polynomial ℂ) (cc b : ℂ)
    (hv : p.eval cc ≠ 0) (hb : b ∈ connectedComponentIn (Omega p) cc)
    (hr : p.IsRoot b) :
    b ∈ bottleneckSlitDomain p cc := by
  refine ⟨hb, ?_⟩
  rw [show p.eval b = 0 from hr]
  exact zero_not_mem_bottleneckSlit (p.eval cc) hv



/-! ## Crossing every circle inside each sheet -/
end Erdos1041.Counterexample

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (r₀ : ℝ)
    (hnear : ∀ z ∈ connectedComponentIn (Omega p) cc,
      p.eval z ∈ bottleneckSlit (p.eval cc) → ‖z - cc‖ < r₀)
    (K : Set ℂ) (hK : IsPreconnected K)
    (hKsub : K ⊆ connectedComponentIn (Omega p) cc)
    (hK₁ : b₁ ∈ K) (hK₂ : b₂ ∈ K)
    (r : ℝ) (hr : r ∈ Set.Ico r₀ ‖b₁ - cc‖) :
    ∃ z ∈ K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁, ‖z - cc‖ = r := by
  have hDopen : IsOpen (bottleneckSlitDomain p cc) := bottleneckSlitDomain_isOpen p cc hv
  have hD₁open : IsOpen (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
    hDopen.connectedComponentIn
  have hD₁pre : IsPreconnected (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
    isPreconnected_connectedComponentIn
  have hD₁D : connectedComponentIn (bottleneckSlitDomain p cc) b₁ ⊆
      bottleneckSlitDomain p cc :=
    connectedComponentIn_subset _ _
  have hb₁D : b₁ ∈ bottleneckSlitDomain p cc :=
    bottleneck_root_mem_slitDomain p cc b₁ hv hb₁ hr₁
  have hb₁D₁ : b₁ ∈ connectedComponentIn (bottleneckSlitDomain p cc) b₁ :=
    mem_connectedComponentIn hb₁D
  have hnormcont : Continuous fun w : ℂ => ‖w - cc‖ := by fun_prop
  have hclosedOuter : IsClosed {w : ℂ | r ≤ ‖w - cc‖} :=
    isClosed_le continuous_const hnormcont
  -- A point of `K` in the closure of the outer part of the sheet lies in the sheet.
  have hclosure : ∀ z ∈ K,
      z ∈ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r ≤ ‖w - cc‖}) →
      z ∈ connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∧ r ≤ ‖z - cc‖ := by
    intro z hzK hzcl
    have hzr : r ≤ ‖z - cc‖ :=
      (closure_minimal Set.inter_subset_right hclosedOuter) hzcl
    have hzD : z ∈ bottleneckSlitDomain p cc := by
      refine ⟨hKsub hzK, fun hslit => ?_⟩
      have hlt := hnear z (hKsub hzK) hslit
      linarith [hr.1]
    have hzcl₁ : z ∈ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
      closure_mono Set.inter_subset_left hzcl
    have hpre : IsPreconnected
        (insert z (connectedComponentIn (bottleneckSlitDomain p cc) b₁)) :=
      hD₁pre.subset_closure (Set.subset_insert _ _)
        (Set.insert_subset hzcl₁ subset_closure)
    have hsub : insert z (connectedComponentIn (bottleneckSlitDomain p cc) b₁) ⊆
        bottleneckSlitDomain p cc :=
      Set.insert_subset hzD hD₁D
    exact ⟨hpre.subset_connectedComponentIn (Set.mem_insert_of_mem z hb₁D₁) hsub
      (Set.mem_insert z _), hzr⟩
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hb₂not : b₂ ∉ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r ≤ ‖w - cc‖}) := by
    intro hcl
    exact bottleneck_preconnected_not_both_roots p cc hv hcover b₁ b₂ hne hr₁ hr₂
      _ hD₁pre hD₁D hb₁D₁ (hclosure b₂ hK₂ hcl).1
  have hU : IsOpen (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r < ‖w - cc‖}) :=
    hD₁open.inter (isOpen_lt continuous_const hnormcont)
  have hV : IsOpen (closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r ≤ ‖w - cc‖}))ᶜ :=
    isClosed_closure.isOpen_compl
  have hcov : K ⊆ (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r < ‖w - cc‖}) ∪
      (closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r ≤ ‖w - cc‖}))ᶜ := by
    intro z hzK
    by_cases hzcl : z ∈ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r ≤ ‖w - cc‖})
    · left
      obtain ⟨hz₁, hzr⟩ := hclosure z hzK hzcl
      exact ⟨hz₁, lt_of_le_of_ne hzr (fun h => hno z ⟨hzK, hz₁⟩ h.symm)⟩
    · exact Or.inr hzcl
  have hne₁ : (K ∩ (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r < ‖w - cc‖})).Nonempty :=
    ⟨b₁, hK₁, hb₁D₁, hr.2⟩
  have hne₂ : (K ∩ (closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r ≤ ‖w - cc‖}))ᶜ).Nonempty :=
    ⟨b₂, hK₂, hb₂not⟩
  obtain ⟨z, -, hzU, hzV⟩ := hK _ _ hU hV hcov hne₁ hne₂
  exact hzV (subset_closure ⟨hzU.1, (show r < ‖z - cc‖ from hzU.2).le⟩)
