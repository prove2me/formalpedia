-- Prove2me | solution 1 for Erdos1041.Counterexample.erdos1041_hausdorff_negation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-30T01:41:12.657127+00:00
-- url     : https://prove2.me/submissions/00605936-8fb2-4fc0-9db9-3a9c3ba66627

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceCritical
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceConnectivity
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_HausdorffLength
import Theorems.Thm_Erdos1041_Counterexample_erdos1041_counterexample
import Theorems.Thm_Erdos1041_Counterexample_erdos1041_counterexample_hausdorff
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





/-! ## Crossing every circle inside each sheet -/



/-! ## From radial crossings to Hausdorff measure -/





/-! ## The instance `f` -/



/-! ## The Formal Conjectures parent, in its own vocabulary -/



/-- The image of a path joining two distinct roots of `f` inside `Ω(f)` has
Hausdorff length greater than two. -/
theorem erdos1041_path_range_hausdorff (z₁ z₂ : ℂ) (hr₁ : f.IsRoot z₁)
    (hr₂ : f.IsRoot z₂) (hne : z₁ ≠ z₂) (γ : Path z₁ z₂)
    (hsub : Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1}) :
    (2 : ℝ≥0∞) < fcLength (Set.range γ) :=
  erdos1041_counterexample_hausdorff z₁ z₂ hr₁ hr₂ hne (Set.range γ)
    (isPreconnected_range γ.continuous) ⟨0, γ.source⟩ ⟨1, γ.target⟩ hsub

-- The binder `h` below is unused, exactly as in the upstream statement this restates.
end Erdos1041.Counterexample

open Erdos1041 in
open Erdos1041.Counterexample in
set_option linter.unusedVariables false in

theorem solution :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by
  intro huniv
  obtain ⟨hmonic, hdeg, hdisk, hnodup, -⟩ := erdos1041_counterexample
  have hn : (7 : ℕ) ≥ 2 := by norm_num
  have hrootset : f.rootSet ℂ ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hzroot : f.IsRoot z := by
      rw [IsRoot, ← coe_aeval_eq_eval]
      exact hmonic.mem_rootSet.mp hz
    simpa [mem_ball, dist_zero_right] using hdisk z hzroot
  obtain ⟨z₁, z₂, hle, γ, hsub, hlen⟩ := huniv 7 f hn hdeg hmonic hrootset
  have hz1_mem : z₁ ∈ f.roots := by
    have hpos : 0 < ({z₁, z₂} : Multiset ℂ).count z₁ := by
      simp [Multiset.count_singleton]
    exact Multiset.count_pos.mp
      (lt_of_lt_of_le hpos ((Multiset.le_iff_count.mp hle) z₁))
  have hz2_mem : z₂ ∈ f.roots := by
    have hpos : 0 < ({z₁, z₂} : Multiset ℂ).count z₂ := by
      simp [Multiset.count_cons]
    exact Multiset.count_pos.mp
      (lt_of_lt_of_le hpos ((Multiset.le_iff_count.mp hle) z₂))
  have hz1 : f.IsRoot z₁ := (mem_roots hmonic.ne_zero).mp hz1_mem
  have hz2 : f.IsRoot z₂ := (mem_roots hmonic.ne_zero).mp hz2_mem
  have hne : z₁ ≠ z₂ := by
    intro heq
    have htwo : 2 ≤ f.roots.count z₁ := by
      have hpair : ({z₁, z₂} : Multiset ℂ).count z₁ = 2 := by
        simp [heq]
      exact hpair ▸ (Multiset.le_iff_count.mp hle) z₁
    have hone : f.roots.count z₁ ≤ 1 :=
      (Multiset.nodup_iff_count_le_one.mp hnodup) z₁
    exact (Nat.not_succ_le_self 1) (le_trans htwo hone)
  exact lt_asymm (erdos1041_path_range_hausdorff z₁ z₂ hz1 hz2 hne γ hsub) hlen
