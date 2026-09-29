-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_fibre_le_two
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:38:14.698993+00:00
-- url     : https://prove2.me/submissions/13dddb13-a051-4f44-909c-0f77a80dc14d

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_locPathConnected
import Theorems.Thm_Erdos1041_Counterexample_zero_not_mem_bottleneckSlit
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_simplyConnected
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
    (e₁ e₂ e₃ : bottleneckSlitDomain p cc)
    (h12 : bottleneckSlitProjection p cc e₁ = bottleneckSlitProjection p cc e₂)
    (h13 : bottleneckSlitProjection p cc e₁ = bottleneckSlitProjection p cc e₃) :
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃ := by
  letI : SimplyConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_simplyConnected (p.eval cc) hv
  letI : LocPathConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_locPathConnected (p.eval cc) hv
  have hzeroBase : (0 : ℂ) ∈ bottleneckSlitBase (p.eval cc) :=
    ⟨by simp, zero_not_mem_bottleneckSlit (p.eval cc) hv⟩
  have hslit₁ : p.eval b₁ ∉ bottleneckSlit (p.eval cc) := by
    rw [show p.eval b₁ = 0 from hr₁]
    exact zero_not_mem_bottleneckSlit (p.eval cc) hv
  have hslit₂ : p.eval b₂ ∉ bottleneckSlit (p.eval cc) := by
    rw [show p.eval b₂ = 0 from hr₂]
    exact zero_not_mem_bottleneckSlit (p.eval cc) hv
  have hB₁ : b₁ ∈ bottleneckSlitDomain p cc := ⟨hb₁, hslit₁⟩
  have hB₂ : b₂ ∈ bottleneckSlitDomain p cc := ⟨hb₂, hslit₂⟩
  have hπB₁ : bottleneckSlitProjection p cc ⟨b₁, hB₁⟩ = ⟨0, hzeroBase⟩ :=
    Subtype.ext (show p.eval b₁ = 0 from hr₁)
  have hπB₂ : bottleneckSlitProjection p cc ⟨b₂, hB₂⟩ = ⟨0, hzeroBase⟩ :=
    Subtype.ext (show p.eval b₂ = 0 from hr₂)
  obtain ⟨σ₁, ⟨hσ₁0, hσ₁π⟩, hσ₁u⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id (bottleneckSlitBase (p.eval cc))) ⟨0, hzeroBase⟩ ⟨b₁, hB₁⟩ hπB₁
  obtain ⟨σ₂, ⟨hσ₂0, hσ₂π⟩, hσ₂u⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id (bottleneckSlitBase (p.eval cc))) ⟨0, hzeroBase⟩ ⟨b₂, hB₂⟩ hπB₂
  have key : ∀ e : bottleneckSlitDomain p cc,
      e = σ₁ (bottleneckSlitProjection p cc e) ∨
      e = σ₂ (bottleneckSlitProjection p cc e) := by
    intro e
    obtain ⟨σ, ⟨hσ0, hσπ⟩, -⟩ := hcover.existsUnique_continuousMap_lifts
      (ContinuousMap.id (bottleneckSlitBase (p.eval cc)))
      (bottleneckSlitProjection p cc e) e rfl
    have hsec : bottleneckSlitProjection p cc (σ ⟨0, hzeroBase⟩) = ⟨0, hzeroBase⟩ :=
      congrFun hσπ ⟨0, hzeroBase⟩
    have hroot : p.IsRoot ((σ ⟨0, hzeroBase⟩ : bottleneckSlitDomain p cc) : ℂ) :=
      congrArg Subtype.val hsec
    have hmem : ((σ ⟨0, hzeroBase⟩ : bottleneckSlitDomain p cc) : ℂ) ∈
        connectedComponentIn (Omega p) cc := (σ ⟨0, hzeroBase⟩).2.1
    rcases hzeros _ hmem hroot with hb | hb
    · exact Or.inl (by rw [← hσ₁u σ ⟨Subtype.ext hb, hσπ⟩]; exact hσ0.symm)
    · exact Or.inr (by rw [← hσ₂u σ ⟨Subtype.ext hb, hσπ⟩]; exact hσ0.symm)
  have h23 : bottleneckSlitProjection p cc e₂ = bottleneckSlitProjection p cc e₃ :=
    h12.symm.trans h13
  have same : ∀ (σ : ContinuousMap (bottleneckSlitBase (p.eval cc))
        (bottleneckSlitDomain p cc)) (a b : bottleneckSlitDomain p cc),
      a = σ (bottleneckSlitProjection p cc a) →
      b = σ (bottleneckSlitProjection p cc b) →
      bottleneckSlitProjection p cc a = bottleneckSlitProjection p cc b → a = b := by
    intro σ a b ha hb hab
    rw [ha, hb, hab]
  rcases key e₁ with k1 | k1 <;> rcases key e₂ with k2 | k2 <;> rcases key e₃ with k3 | k3
  · exact Or.inl (same σ₁ e₁ e₂ k1 k2 h12)
  · exact Or.inl (same σ₁ e₁ e₂ k1 k2 h12)
  · exact Or.inr (Or.inl (same σ₁ e₁ e₃ k1 k3 h13))
  · exact Or.inr (Or.inr (same σ₂ e₂ e₃ k2 k3 h23))
  · exact Or.inr (Or.inr (same σ₁ e₂ e₃ k2 k3 h23))
  · exact Or.inr (Or.inl (same σ₂ e₁ e₃ k1 k3 h13))
  · exact Or.inl (same σ₂ e₁ e₂ k1 k2 h12)
  · exact Or.inl (same σ₂ e₁ e₂ k1 k2 h12)
