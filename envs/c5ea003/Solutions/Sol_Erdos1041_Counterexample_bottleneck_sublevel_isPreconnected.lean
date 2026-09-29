-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_sublevel_isPreconnected
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:28:05.451992+00:00
-- url     : https://prove2.me/submissions/8d1bb596-a3d3-4036-8b81-a45a9303c88c

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
theorem solution (f : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hdiff : DifferentiableOn ℂ f V) (c : ℂ) (hc : c ∈ V) (m : ℝ) (hm : ‖f c‖ < m)
    (hzero : ∀ z ∈ V, f z = 0 → z = c)
    (hbdd : Bornology.IsBounded {z | z ∈ V ∧ ‖f z‖ < m})
    (hcl : closure {z | z ∈ V ∧ ‖f z‖ < m} ⊆ V) :
    IsPreconnected {z | z ∈ V ∧ ‖f z‖ < m} := by
  set Y : Set ℂ := {z | z ∈ V ∧ ‖f z‖ < m} with hYdef
  have hfcont : ContinuousOn f V := hdiff.continuousOn
  have hYopen : IsOpen Y :=
    hfcont.isOpen_inter_preimage hV (isOpen_lt continuous_norm continuous_const)
  have hcY : c ∈ Y := ⟨hc, hm⟩
  have key : ∀ u v : Set ℂ, IsOpen u → IsOpen v → Y ⊆ u ∪ v → c ∈ u →
      Y ∩ (u ∩ v) = ∅ → (Y ∩ v).Nonempty → False := by
    intro u v hu hv hsub hcu hempty hne
    have hmeet : ∀ x : ℂ, x ∈ Y → x ∈ u → x ∈ v → False := by
      intro x hxY hxu hxv
      exact Set.eq_empty_iff_forall_notMem.mp hempty x ⟨hxY, hxu, hxv⟩
    set Y₁ : Set ℂ := Y ∩ v with hY₁def
    have hY₁open : IsOpen Y₁ := hYopen.inter hv
    have hY₁sub : Y₁ ⊆ Y := Set.inter_subset_left
    have hclY₁ : ∀ w, w ∈ closure Y₁ → w ∈ Y → w ∈ Y₁ := by
      intro w hwc hwY
      by_contra hwn
      have hwu : u ∈ nhds w := by
        rcases hsub hwY with hwu | hwv
        · exact hu.mem_nhds hwu
        · exact absurd ⟨hwY, hwv⟩ hwn
      obtain ⟨x, hxu, hxY, hxv⟩ := mem_closure_iff_nhds.mp hwc u hwu
      exact hmeet x hxY hxu hxv
    have hcnot : c ∉ closure Y₁ := by
      intro hcc
      obtain ⟨x, hxu, hxY, hxv⟩ := mem_closure_iff_nhds.mp hcc u (hu.mem_nhds hcu)
      exact hmeet x hxY hxu hxv
    have hclsub : closure Y₁ ⊆ V :=
      (closure_mono hY₁sub).trans hcl
    have hfne : ∀ w ∈ closure Y₁, f w ≠ 0 := by
      intro w hw hw0
      exact hcnot ((hzero w (hclsub hw) hw0) ▸ hw)
    have hdc : DiffContOnCl ℂ (fun w => (f w)⁻¹) Y₁ := by
      refine ⟨(hdiff.mono (fun z hz => (hY₁sub hz).1)).inv
        (fun w hw => hfne w (subset_closure hw)), ?_⟩
      exact (hfcont.mono hclsub).inv₀ hfne
    obtain ⟨z, hzf, hzmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
      (hbdd.subset hY₁sub) hne hdc
    rw [hY₁open.frontier_eq] at hzf
    obtain ⟨hzcl, hznotY₁⟩ := hzf
    have hzV : z ∈ V := hclsub hzcl
    have hzm : m ≤ ‖f z‖ := by
      by_contra hlt
      exact hznotY₁ (hclY₁ z hzcl ⟨hzV, lt_of_not_ge hlt⟩)
    obtain ⟨x, hxY, hxv⟩ := hne
    have hxcl : x ∈ closure Y₁ := subset_closure ⟨hxY, hxv⟩
    have hmax : ‖(f x)⁻¹‖ ≤ ‖(f z)⁻¹‖ := hzmax hxcl
    rw [norm_inv, norm_inv] at hmax
    have hxpos : 0 < ‖f x‖ := norm_pos_iff.mpr (hfne x hxcl)
    have hzpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hfne z hzcl)
    have : ‖f z‖ ≤ ‖f x‖ := (inv_le_inv₀ hxpos hzpos).mp hmax
    exact absurd hxY.2 (not_lt.mpr (hzm.trans this))
  intro u v hu hv hsub h1 h2
  by_contra hcon
  have hempty : Y ∩ (u ∩ v) = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
  rcases hsub hcY with hcu | hcv
  · exact absurd (key u v hu hv hsub hcu hempty h2) not_false
  · refine absurd (key v u hv hu (fun z hz => (hsub hz).symm) hcv ?_ h1) not_false
    rw [Set.inter_comm u v] at hempty
    exact hempty
