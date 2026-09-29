-- Prove2me | solution 1 for Erdos1041.Counterexample.s2_two_zeros_gives_critical_point
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:36:38.109391+00:00
-- url     : https://prove2.me/submissions/133f685d-94b2-4032-b283-d8cfdb58a351

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Theorems.Thm_Erdos1041_Counterexample_s2_isClosedEmbedding_componentIn_inclusion
import Theorems.Thm_Erdos1041_Counterexample_s2_covering_injective
import Theorems.Thm_Erdos1041_Counterexample_s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
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
Formalisation of Lemma 2.1 from `ani_degree7_counterexample.tex`. -/

/-
Integration: move the S2 declaration out of Defs before importing this module.
The supplied Defs is preserved under input/; see DEFS_DELTAS.md.
Repaired and compiled against Mathlib v4.29.1 (commit 5e932f97).
-/

noncomputable section

open Set Filter Topology

open Erdos1041 in
open Erdos1041.Counterexample in
theorem solution
    (p : Polynomial ℂ) (hp : 0 < p.natDegree) (z : ℂ) (hz : z ∈ Omega p)
    (w₁ w₂ : ℂ) (hw₁ : w₁ ∈ connectedComponentIn (Omega p) z)
    (hw₂ : w₂ ∈ connectedComponentIn (Omega p) z) (hne : w₁ ≠ w₂)
    (hr₁ : p.IsRoot w₁) (hr₂ : p.IsRoot w₂) :
    ∃ cc ∈ connectedComponentIn (Omega p) z, (Polynomial.derivative p).IsRoot cc := by
  classical
  by_contra hcrit
  have hderiv : ∀ u ∈ connectedComponentIn (Omega p) z,
      (Polynomial.derivative p).eval u ≠ 0 := by
    intro u hu hzero
    exact hcrit ⟨u, hu, hzero⟩
  let D : Set ℂ := {w : ℂ | ‖w‖ < 1}
  let U : Set ℂ := connectedComponentIn (Omega p) z
  have hDopen : IsOpen D := isOpen_lt continuous_norm continuous_const
  have hOopen : IsOpen (Omega p) := isOpen_lt p.continuous.norm continuous_const
  have hUopen : IsOpen U := hOopen.connectedComponentIn
  have hUsub : U ⊆ Omega p := connectedComponentIn_subset (Omega p) z
  let q : U → D := fun u => ⟨p.eval u.val, hUsub u.property⟩
  have hqcont : Continuous q :=
    (p.continuous.comp continuous_subtype_val).subtype_mk _
  -- The polynomial is proper; restrict its base to D and its domain to the
  -- relatively closed component. No assertion that U is closed in ℂ is used.
  have hpdegree : 0 < p.degree := by
    apply lt_of_not_ge
    intro h
    exact (not_le_of_gt hp) (Polynomial.natDegree_le_of_degree_le h)
  have hpglobal : IsProperMap p.eval := p.isProperMap_eval hpdegree
  have hqproper : IsProperMap q := by
    have hpD := hpglobal.restrictPreimage D
    have hinc := (s2_isClosedEmbedding_componentIn_inclusion hz).isProperMap
    exact hpD.comp hinc
  -- Non-vanishing of p' supplies inverse-function charts on U.
  have hpLocal : IsLocalHomeomorphOn p.eval U := by
    intro u hu
    have hd := (p.hasStrictDerivAt u).hasStrictFDerivAt_equiv (hderiv u hu)
    exact ⟨hd.toOpenPartialHomeomorph p.eval,
      hd.mem_toOpenPartialHomeomorph_source, rfl⟩
  have hUinc : IsLocalHomeomorph (Subtype.val : U → ℂ) :=
    hUopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hscalar : IsLocalHomeomorph (fun u : U => p.eval u.val) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hpLocal.comp hUinc.isLocalHomeomorphOn (fun u _ => u.property))
  have hDinc : IsLocalHomeomorph (Subtype.val : D → ℂ) :=
    hDopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hqlocal : IsLocalHomeomorph q := hscalar.of_comp hDinc hqcont
  have hqcover : IsCoveringMap q :=
    s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph hqproper hqlocal
  -- Only the disc, not the lemniscate component, needs to be simply connected.
  have hDconvex : Convex ℝ D := by
    have hball : Convex ℝ (Metric.ball (0 : ℂ) (1 : ℝ)) := convex_ball _ _
    simpa only [D, Metric.ball, dist_zero_right] using hball
  have hDzero : (0 : ℂ) ∈ D := by simp [D]
  letI : ContractibleSpace D := hDconvex.contractibleSpace ⟨0, hDzero⟩
  letI : SimplyConnectedSpace D := SimplyConnectedSpace.ofContractible D
  letI : LocPathConnectedSpace D := hDopen.locPathConnectedSpace
  letI : ConnectedSpace U :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hz)
  have hqinj : Function.Injective q := s2_covering_injective hqcover
  have heq : q ⟨w₁, hw₁⟩ = q ⟨w₂, hw₂⟩ := by
    apply Subtype.ext
    change p.eval w₁ = p.eval w₂
    exact (show p.eval w₁ = 0 from hr₁).trans (show p.eval w₂ = 0 from hr₂).symm
  exact hne (congrArg Subtype.val (hqinj heq))
