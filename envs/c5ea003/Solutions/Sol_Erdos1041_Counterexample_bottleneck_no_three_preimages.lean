-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_no_three_preimages
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:48:44.371978+00:00
-- url     : https://prove2.me/submissions/322ce01a-bf1a-44e1-b5bf-8cd8f7fa11c2

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlit_mem_closure_base
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_fibre_le_two
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
theorem solution (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (ξ : ℂ) (hξ : ξ ∈ bottleneckSlit (p.eval cc)) (hξv : ξ ≠ p.eval cc)
    (w₁ w₂ w₃ : ℂ)
    (hw₁ : w₁ ∈ connectedComponentIn (Omega p) cc)
    (hw₂ : w₂ ∈ connectedComponentIn (Omega p) cc)
    (hw₃ : w₃ ∈ connectedComponentIn (Omega p) cc)
    (hp₁ : p.eval w₁ = ξ) (hp₂ : p.eval w₂ = ξ) (hp₃ : p.eval w₃ = ξ)
    (n12 : w₁ ≠ w₂) (n13 : w₁ ≠ w₃) (n23 : w₂ ≠ w₃) : False := by
  have hOopen : IsOpen (Omega p) := isOpen_lt p.continuous.norm continuous_const
  have hUopen : IsOpen (connectedComponentIn (Omega p) cc) := hOopen.connectedComponentIn
  have hreg : ∀ w ∈ connectedComponentIn (Omega p) cc, p.eval w = ξ →
      (Polynomial.derivative p).eval w ≠ 0 := by
    intro w hw hpw hzero
    rw [huniq w hw hzero] at hpw
    exact hξv hpw.symm
  have hloc : ∀ w : ℂ, (Polynomial.derivative p).eval w ≠ 0 →
      ∃ e : OpenPartialHomeomorph ℂ ℂ, w ∈ e.source ∧ p.eval = ⇑e := by
    intro w hw
    have hd := (p.hasStrictDerivAt w).hasStrictFDerivAt_equiv hw
    exact ⟨hd.toOpenPartialHomeomorph p.eval, hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  obtain ⟨c₁, hc₁, he₁⟩ := hloc w₁ (hreg w₁ hw₁ hp₁)
  obtain ⟨c₂, hc₂, he₂⟩ := hloc w₂ (hreg w₂ hw₂ hp₂)
  obtain ⟨c₃, hc₃, he₃⟩ := hloc w₃ (hreg w₃ hw₃ hp₃)
  have d12 : 0 < dist w₁ w₂ := dist_pos.mpr n12
  have d13 : 0 < dist w₁ w₃ := dist_pos.mpr n13
  have d23 : 0 < dist w₂ w₃ := dist_pos.mpr n23
  set r : ℝ := min (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃)) / 3 with hrdef
  have hrpos : 0 < r := by
    have := lt_min d12 (lt_min d13 d23)
    simp only [hrdef]
    linarith
  have hr12 : 3 * r ≤ dist w₁ w₂ := by
    simp only [hrdef]
    have := min_le_left (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃))
    linarith
  have hr13 : 3 * r ≤ dist w₁ w₃ := by
    simp only [hrdef]
    have h1 := min_le_right (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃))
    have h2 := min_le_left (dist w₁ w₃) (dist w₂ w₃)
    linarith
  have hr23 : 3 * r ≤ dist w₂ w₃ := by
    simp only [hrdef]
    have h1 := min_le_right (dist w₁ w₂) (min (dist w₁ w₃) (dist w₂ w₃))
    have h2 := min_le_right (dist w₁ w₃) (dist w₂ w₃)
    linarith
  -- the three separated inverse charts
  set V₁ : Set ℂ := c₁.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball w₁ r with hV₁
  set V₂ : Set ℂ := c₂.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball w₂ r with hV₂
  set V₃ : Set ℂ := c₃.source ∩ connectedComponentIn (Omega p) cc ∩ Metric.ball w₃ r with hV₃
  have hV₁open : IsOpen V₁ := (c₁.open_source.inter hUopen).inter Metric.isOpen_ball
  have hV₂open : IsOpen V₂ := (c₂.open_source.inter hUopen).inter Metric.isOpen_ball
  have hV₃open : IsOpen V₃ := (c₃.open_source.inter hUopen).inter Metric.isOpen_ball
  have hw₁V : w₁ ∈ V₁ := ⟨⟨hc₁, hw₁⟩, Metric.mem_ball_self hrpos⟩
  have hw₂V : w₂ ∈ V₂ := ⟨⟨hc₂, hw₂⟩, Metric.mem_ball_self hrpos⟩
  have hw₃V : w₃ ∈ V₃ := ⟨⟨hc₃, hw₃⟩, Metric.mem_ball_self hrpos⟩
  have himg₁ : IsOpen (c₁ '' V₁) :=
    c₁.isOpen_image_of_subset_source hV₁open (fun x hx => hx.1.1)
  have himg₂ : IsOpen (c₂ '' V₂) :=
    c₂.isOpen_image_of_subset_source hV₂open (fun x hx => hx.1.1)
  have himg₃ : IsOpen (c₃ '' V₃) :=
    c₃.isOpen_image_of_subset_source hV₃open (fun x hx => hx.1.1)
  have hξ₁ : ξ ∈ c₁ '' V₁ := ⟨w₁, hw₁V, (congrFun he₁ w₁).symm.trans hp₁⟩
  have hξ₂ : ξ ∈ c₂ '' V₂ := ⟨w₂, hw₂V, (congrFun he₂ w₂).symm.trans hp₂⟩
  have hξ₃ : ξ ∈ c₃ '' V₃ := ⟨w₃, hw₃V, (congrFun he₃ w₃).symm.trans hp₃⟩
  have hTopen : IsOpen ((c₁ '' V₁) ∩ (c₂ '' V₂) ∩ (c₃ '' V₃)) :=
    (himg₁.inter himg₂).inter himg₃
  have hξT : ξ ∈ (c₁ '' V₁) ∩ (c₂ '' V₂) ∩ (c₃ '' V₃) := ⟨⟨hξ₁, hξ₂⟩, hξ₃⟩
  obtain ⟨ξ', ⟨⟨hξ'₁, hξ'₂⟩, hξ'₃⟩, hξ'base⟩ :=
    mem_closure_iff.mp (bottleneckSlit_mem_closure_base (p.eval cc) hv ξ hξ) _ hTopen hξT
  obtain ⟨y₁, hy₁V, hy₁⟩ := hξ'₁
  obtain ⟨y₂, hy₂V, hy₂⟩ := hξ'₂
  obtain ⟨y₃, hy₃V, hy₃⟩ := hξ'₃
  have hpy₁ : p.eval y₁ = ξ' := (congrFun he₁ y₁).trans hy₁
  have hpy₂ : p.eval y₂ = ξ' := (congrFun he₂ y₂).trans hy₂
  have hpy₃ : p.eval y₃ = ξ' := (congrFun he₃ y₃).trans hy₃
  have hdom : ∀ y : ℂ, y ∈ connectedComponentIn (Omega p) cc → p.eval y = ξ' →
      y ∈ bottleneckSlitDomain p cc := by
    intro y hy hpy
    exact ⟨hy, by rw [hpy]; exact hξ'base.2⟩
  have hD₁ := hdom y₁ hy₁V.1.2 hpy₁
  have hD₂ := hdom y₂ hy₂V.1.2 hpy₂
  have hD₃ := hdom y₃ hy₃V.1.2 hpy₃
  have hproj₁₂ : bottleneckSlitProjection p cc ⟨y₁, hD₁⟩ =
      bottleneckSlitProjection p cc ⟨y₂, hD₂⟩ := Subtype.ext (hpy₁.trans hpy₂.symm)
  have hproj₁₃ : bottleneckSlitProjection p cc ⟨y₁, hD₁⟩ =
      bottleneckSlitProjection p cc ⟨y₃, hD₃⟩ := Subtype.ext (hpy₁.trans hpy₃.symm)
  -- the three lifts are distinct because the charts were separated
  have hsep : ∀ (a b u v : ℂ) (ra : ℝ), 3 * ra ≤ dist u v →
      a ∈ Metric.ball u ra → b ∈ Metric.ball v ra → 0 < ra → a ≠ b := by
    intro a b u v ra hd ha hb hra hab
    subst hab
    have h1 : dist u a < ra := by
      rw [dist_comm]
      exact Metric.mem_ball.mp ha
    have h2 : dist a v < ra := Metric.mem_ball.mp hb
    have := dist_triangle u a v
    linarith
  have n₁₂ : y₁ ≠ y₂ := hsep y₁ y₂ w₁ w₂ r hr12 hy₁V.2 hy₂V.2 hrpos
  have n₁₃ : y₁ ≠ y₃ := hsep y₁ y₃ w₁ w₃ r hr13 hy₁V.2 hy₃V.2 hrpos
  have n₂₃ : y₂ ≠ y₃ := hsep y₂ y₃ w₂ w₃ r hr23 hy₂V.2 hy₃V.2 hrpos
  rcases bottleneck_fibre_le_two p cc hv hcover b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros
    ⟨y₁, hD₁⟩ ⟨y₂, hD₂⟩ ⟨y₃, hD₃⟩ hproj₁₂ hproj₁₃ with hq | hq | hq
  · exact n₁₂ (congrArg Subtype.val hq)
  · exact n₁₃ (congrArg Subtype.val hq)
  · exact n₂₃ (congrArg Subtype.val hq)
