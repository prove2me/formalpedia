-- Prove2me | solution 1 for Erdos1041.Counterexample.s3_bottleneck_hausdorff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:21:29.391207+00:00
-- url     : https://prove2.me/submissions/e31e07dc-aed2-4136-a392-b4e34722768f

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
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_natDegree_pos
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_preconnected_not_both_roots
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_sheet_crossing
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_slit_preimage_near
import Theorems.Thm_Erdos1041_Counterexample_s3_bottleneck_isCoveringMap
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



/-! ## From radial crossings to Hausdorff measure -/

/-- The distance to a point is 1-Lipschitz, and `μH[1]` on `ℝ` is Lebesgue
measure, so the radial image of a set is no longer than the set. -/
theorem volume_dist_image_le_hausdorff (cc : ℂ) (S : Set ℂ) :
    volume ((fun z : ℂ => dist z cc) '' S) ≤ μH[1] S := by
  have h := (LipschitzWith.dist_left cc).hausdorffMeasure_image_le
    (zero_le_one : (0 : ℝ) ≤ 1) S
  rw [hausdorffMeasure_real] at h
  simpa using h
end Erdos1041.Counterexample

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (K : Set ℂ) (hK : IsPreconnected K)
    (hKsub : K ⊆ connectedComponentIn (Omega p) cc)
    (hK₁ : b₁ ∈ K) (hK₂ : b₂ ∈ K) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ μH[1] K := by
  have hdeg := bottleneck_natDegree_pos p cc b₁ hv hr₁
  have hcover := s3_bottleneck_isCoveringMap p cc hcc hv hdeg huniq
  have hnear : ∀ z ∈ connectedComponentIn (Omega p) cc,
      p.eval z ∈ bottleneckSlit (p.eval cc) →
        ‖z - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖) := fun z hz hslit =>
    bottleneck_slit_preimage_near p cc hcrit hv hcover aHat haHat h hh hdisk δ hδ
      hδpos hδsmall b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq z hz hslit
  have hD₁open : IsOpen (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
    (bottleneckSlitDomain_isOpen p cc hv).connectedComponentIn
  have hb₁D : b₁ ∈ bottleneckSlitDomain p cc :=
    bottleneck_root_mem_slitDomain p cc b₁ hv hb₁ hr₁
  have hb₂D : b₂ ∈ bottleneckSlitDomain p cc :=
    bottleneck_root_mem_slitDomain p cc b₂ hv hb₂ hr₂
  -- The components of the two roots are disjoint.
  have hdisj : Disjoint (connectedComponentIn (bottleneckSlitDomain p cc) b₁)
      (connectedComponentIn (bottleneckSlitDomain p cc) b₂) := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have heq₁ : connectedComponentIn (bottleneckSlitDomain p cc) b₁ =
        connectedComponentIn (bottleneckSlitDomain p cc) z := connectedComponentIn_eq hz₁
    have heq₂ : connectedComponentIn (bottleneckSlitDomain p cc) b₂ =
        connectedComponentIn (bottleneckSlitDomain p cc) z := connectedComponentIn_eq hz₂
    have hb₂D₁ : b₂ ∈ connectedComponentIn (bottleneckSlitDomain p cc) b₁ := by
      rw [heq₁, ← heq₂]
      exact mem_connectedComponentIn hb₂D
    exact bottleneck_preconnected_not_both_roots p cc hv hcover b₁ b₂ hne hr₁ hr₂
      _ isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn hb₁D) hb₂D₁
  -- Radial images of the two sheets.
  have himg₁ : Set.Ico (4 / 3 * Real.sqrt (δ / ‖aHat‖)) ‖b₁ - cc‖ ⊆
      (fun z : ℂ => dist z cc) ''
        (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := bottleneck_sheet_crossing p cc hv hcover b₁ b₂ hne hr₁ hr₂
      hb₁ _ hnear K hK hKsub hK₁ hK₂ r hr
    exact ⟨z, hz, (dist_eq_norm z cc).trans hzr⟩
  have himg₂ : Set.Ico (4 / 3 * Real.sqrt (δ / ‖aHat‖)) ‖b₂ - cc‖ ⊆
      (fun z : ℂ => dist z cc) ''
        (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₂) := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := bottleneck_sheet_crossing p cc hv hcover b₂ b₁ hne.symm
      hr₂ hr₁ hb₂ _ hnear K hK hKsub hK₂ hK₁ r hr
    exact ⟨z, hz, (dist_eq_norm z cc).trans hzr⟩
  have hm₁ : ENNReal.ofReal (‖b₁ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤
      μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) := by
    rw [← Real.volume_Ico]
    exact (measure_mono himg₁).trans (volume_dist_image_le_hausdorff cc _)
  have hm₂ : ENNReal.ofReal (‖b₂ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤
      μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₂) := by
    rw [← Real.volume_Ico]
    exact (measure_mono himg₂).trans (volume_dist_image_le_hausdorff cc _)
  have hsplit : μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) +
      μH[1] (K \ connectedComponentIn (bottleneckSlitDomain p cc) b₁) = μH[1] K :=
    measure_inter_add_diff K hD₁open.measurableSet
  have hdiff : μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₂) ≤
      μH[1] (K \ connectedComponentIn (bottleneckSlitDomain p cc) b₁) := by
    apply measure_mono
    intro z hz
    exact ⟨hz.1, fun hz₁ => Set.disjoint_left.mp hdisj hz₁ hz.2⟩
  calc ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      = ENNReal.ofReal ((‖b₁ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) +
          (‖b₂ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖))) := by
        congr 1
        ring
    _ ≤ ENNReal.ofReal (‖b₁ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) +
          ENNReal.ofReal (‖b₂ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) :=
        ENNReal.ofReal_add_le
    _ ≤ μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) +
          μH[1] (K \ connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
        add_le_add hm₁ (hm₂.trans hdiff)
    _ = μH[1] K := hsplit
