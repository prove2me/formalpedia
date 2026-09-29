-- Prove2me | solution 1 for Erdos1041.Counterexample.bottleneck_path_meets_slit_of_covering
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:38:15.376982+00:00
-- url     : https://prove2.me/submissions/b13e7fa5-a1c5-4eb7-aaab-f8df23b60661

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Bottleneck
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_locPathConnected
import Theorems.Thm_Erdos1041_Counterexample_bottleneckSlitBase_simplyConnected
import Theorems.Thm_Erdos1041_Counterexample_bottleneck_covering_fibre_eq_on_preconnected
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
theorem solution
    (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (γ : ℝ → ℂ) (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hγ0 : γ 0 = b₁) (hγ1 : γ 1 = b₂)
    (hγmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      γ τ ∈ connectedComponentIn (Omega p) cc) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ connectedComponentIn (Omega p) cc ∩
      (fun z => p.eval z) ⁻¹' bottleneckSlit (p.eval cc) := by
  letI : SimplyConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_simplyConnected (p.eval cc) hv
  letI : LocPathConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_locPathConnected (p.eval cc) hv
  by_contra hno
  have havoid (t : Set.Icc (0 : ℝ) 1) :
      p.eval (γ t) ∉ bottleneckSlit (p.eval cc) := by
    intro ht
    exact hno ⟨t, t.2, hγmem t t.2, ht⟩
  let g : Set.Icc (0 : ℝ) 1 → bottleneckSlitDomain p cc :=
    fun t => ⟨γ t, ⟨hγmem t t.2, havoid t⟩⟩
  have hg : Continuous g :=
    (continuousOn_iff_continuous_restrict.mp hcont).subtype_mk _
  let t₀ : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let t₁ : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hbase : bottleneckSlitProjection p cc (g t₀) =
      bottleneckSlitProjection p cc (g t₁) := by
    apply Subtype.ext
    change p.eval (γ 0) = p.eval (γ 1)
    rw [hγ0, hγ1]
    exact (show p.eval b₁ = 0 from hr₁).trans (show p.eval b₂ = 0 from hr₂).symm
  have heq := bottleneck_covering_fibre_eq_on_preconnected
    (bottleneckSlitProjection p cc) hcover Set.univ isPreconnected_univ
    g hg.continuousOn t₀ t₁ (Set.mem_univ _) (Set.mem_univ _) hbase
  have hend : γ 0 = γ 1 := congrArg Subtype.val heq
  exact hne (hγ0.symm.trans (hend.trans hγ1))
