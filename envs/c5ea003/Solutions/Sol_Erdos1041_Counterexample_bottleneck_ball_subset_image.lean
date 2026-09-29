-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_ball_subset_image
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:03.441861+00:00
-- url     : https://prove2.me/submissions/625808d5-96f5-4348-a305-8c99b1b83579

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
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

noncomputable section
open Topology

open Erdos1041
open Erdos1041.Counterexample
open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution (f : ℂ → ℂ) (c : ℂ) (r ε : ℝ) (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.closedBall c r))
    (himg : IsOpen (f '' Metric.ball c r))
    (hsphere : ∀ z ∈ Metric.sphere c r, ε ≤ ‖f z - f c‖) :
    Metric.ball (f c) ε ⊆ f '' Metric.ball c r := by
  have hclosed : IsClosed (f '' Metric.closedBall c r) :=
    ((isCompact_closedBall c r).image_of_continuousOn hcont).isClosed
  -- inside `ball (f c) ε` the two images agree
  have himage : ∀ y ∈ Metric.ball (f c) ε,
      y ∈ f '' Metric.closedBall c r → y ∈ f '' Metric.ball c r := by
    rintro y hy ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
    · exact Metric.mem_ball.mpr hlt
    · exfalso
      have hzs : z ∈ Metric.sphere c r := Metric.mem_sphere.mpr heq
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact absurd (hsphere z hzs) (not_le.mpr hy)
  intro w hw
  by_contra hwnot
  have hεpos : 0 < ε := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw)
  have hconn : IsPreconnected (Metric.ball (f c) ε) :=
    (convex_ball (f c) ε).isPreconnected
  have hcover : Metric.ball (f c) ε ⊆
      (f '' Metric.ball c r) ∪ (f '' Metric.closedBall c r)ᶜ := by
    intro y hy
    by_cases hy' : y ∈ f '' Metric.closedBall c r
    · exact Or.inl (himage y hy hy')
    · exact Or.inr hy'
  have h1 : (Metric.ball (f c) ε ∩ f '' Metric.ball c r).Nonempty :=
    ⟨f c, Metric.mem_ball_self hεpos, ⟨c, Metric.mem_ball_self hr, rfl⟩⟩
  have h2 : (Metric.ball (f c) ε ∩ (f '' Metric.closedBall c r)ᶜ).Nonempty :=
    ⟨w, hw, fun hmem => hwnot (himage w hw hmem)⟩
  obtain ⟨y, -, hy1, hy2⟩ :=
    hconn _ _ himg hclosed.isOpen_compl hcover h1 h2
  exact hy2 (Set.image_mono Metric.ball_subset_closedBall hy1)
