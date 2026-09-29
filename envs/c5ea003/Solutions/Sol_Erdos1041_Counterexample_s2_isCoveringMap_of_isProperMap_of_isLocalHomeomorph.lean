-- Prove2me | solution 1 for Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:31:22.592343+00:00
-- url     : https://prove2.me/submissions/6312b6b3-8626-4c78-9b29-0714d788e637

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
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
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    {g : E → X} (hproper : IsProperMap g) (hlocal : IsLocalHomeomorph g) :
    IsCoveringMap g := by
  classical
  intro x
  let F : Type _ := g ⁻¹' {x}
  have hfibre : IsCompact (g ⁻¹' {x}) :=
    hproper.isCompact_preimage isCompact_singleton
  choose e he_source he_eq using (fun a : F => hlocal a.val)
  -- Compactness and local injectivity make the fibre finite.
  obtain ⟨t, ht⟩ := hfibre.elim_finite_subcover
    (fun a : F => (e a).source) (fun a => (e a).open_source) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, he_source ⟨y, hy⟩⟩)
  have hall : ∀ a : F, a ∈ t := by
    intro a
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (ht a.property)
    have hab' : a = b := by
      apply Subtype.ext
      apply (e b).injOn hab (he_source b)
      rw [← he_eq b]
      exact (show g a.val = x from a.property).trans
        (show g b.val = x from b.property).symm
    exact hab'.symm ▸ hb
  have hfinite : (g ⁻¹' {x}).Finite := by
    have hset : g ⁻¹' {x} = Subtype.val '' (↑t : Set F) := by
      ext y
      constructor
      · intro hy
        exact ⟨⟨y, hy⟩, hall ⟨y, hy⟩, rfl⟩
      · rintro ⟨a, _, rfl⟩
        exact a.property
    rw [hset]
    exact t.finite_toSet.image Subtype.val
  letI : Fintype F := hfinite.fintype
  letI : DiscreteTopology F := discreteTopology_iff_isOpen_singleton.mpr (by
    intro a
    have hset : (Subtype.val : F → E) ⁻¹' (e a).source = {a} := by
      ext b
      constructor
      · intro hb
        apply Subtype.ext
        apply (e a).injOn hb (he_source a)
        rw [← he_eq a]
        exact (show g b.val = x from b.property).trans
          (show g a.val = x from a.property).symm
      · intro hb
        have hba : b = a := hb
        subst b
        exact he_source a
    rw [← hset]
    exact (e a).open_source.preimage continuous_subtype_val)
  -- Separate the finitely many inverse charts in the total space.
  obtain ⟨N, hN, hNdisjoint⟩ := hfinite.t2_separation
  let V : F → Set E := fun a => (e a).source ∩ N a.val
  have hVopen (a : F) : IsOpen (V a) :=
    (e a).open_source.inter (hN a.val).2
  have hVmem (a : F) : a.val ∈ V a := ⟨he_source a, (hN a.val).1⟩
  have hVdisjoint : ∀ a b : F, a ≠ b → Disjoint (V a) (V b) := by
    intro a b hab
    exact (hNdisjoint a.property b.property
      (fun h => hab (Subtype.ext h))).mono inter_subset_right inter_subset_right
  let W : Set X := (⋂ a : F, g '' V a) ∩ (g '' (⋃ a : F, V a)ᶜ)ᶜ
  have hWopen : IsOpen W :=
    (isOpen_iInter_of_finite (fun a => hlocal.isOpenMap _ (hVopen a))).inter
      (hproper.isClosedMap _ (isOpen_iUnion hVopen).isClosed_compl).isOpen_compl
  have hxW : x ∈ W := by
    constructor
    · apply mem_iInter.mpr
      intro a
      exact ⟨a.val, hVmem a, a.property⟩
    · rintro ⟨y, hy, hgy⟩
      exact hy (mem_iUnion.mpr ⟨⟨y, hgy⟩, hVmem ⟨y, hgy⟩⟩)
  have hWpreopen : IsOpen (g ⁻¹' W) := hWopen.preimage hproper.continuous
  have hcover : ∀ y : g ⁻¹' W, ∃ a : F, y.val ∈ V a := by
    intro y
    by_contra h
    apply y.property.2
    refine ⟨y.val, ?_, rfl⟩
    intro hmem
    obtain ⟨a, ha⟩ := mem_iUnion.mp hmem
    exact h ⟨a, ha⟩
  choose idx hidx using hcover
  have hidx_eq {y : g ⁻¹' W} {a : F} (hy : y.val ∈ V a) : idx y = a := by
    by_contra h
    exact (Set.disjoint_left.mp (hVdisjoint (idx y) a h)) (hidx y) hy
  -- Each inverse branch maps W to its designated chart, not merely to the fibre.
  have hinv (a : F) (w : W) :
      (e a).symm w.val ∈ V a ∧ g ((e a).symm w.val) = w.val := by
    obtain ⟨y, hy, hgy⟩ := mem_iInter.mp w.property.1 a
    have heq : (e a).symm w.val = y := by
      rw [← hgy, he_eq a]
      exact (e a).left_inv hy.1
    exact ⟨by rw [heq]; exact hy, by rw [heq]; exact hgy⟩
  have htarget (a : F) (w : W) : w.val ∈ (e a).target := by
    obtain ⟨y, hy, hgy⟩ := mem_iInter.mp w.property.1 a
    rw [← hgy, he_eq a]
    exact (e a).map_source hy.1
  have hidx_cont : Continuous idx := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hn : ∀ᶠ y' in 𝓝 y, y'.val ∈ V (idx y) :=
      ((hVopen (idx y)).preimage continuous_subtype_val).mem_nhds (hidx y)
    have heq : (fun _ : g ⁻¹' W => idx y) =ᶠ[𝓝 y] idx := by
      filter_upwards [hn] with y' hy'
      exact (hidx_eq hy').symm
    exact tendsto_const_nhds.congr' heq
  let H : (g ⁻¹' W) → W × F := fun y => (⟨g y.val, y.property⟩, idx y)
  have hHcont : Continuous H := by
    have hfirst : Continuous (fun y : g ⁻¹' W => (⟨g y.val, y.property⟩ : W)) :=
      (hproper.continuous.comp continuous_subtype_val).subtype_mk _
    exact hfirst.prodMk hidx_cont
  let inv : W × F → E := fun wa => (e wa.2).symm wa.1.val
  have hinv_cont : Continuous inv := by
    apply continuous_iff_continuousAt.mpr
    intro wa
    have hn : ∀ᶠ wb : W × F in 𝓝 wa, wb.2 = wa.2 :=
      (continuous_snd.tendsto wa) ((isOpen_discrete {wa.2}).mem_nhds rfl)
    have heq : (fun wb : W × F => (e wa.2).symm wb.1.val) =ᶠ[𝓝 wa] inv := by
      filter_upwards [hn] with wb hwb
      simp only [inv, hwb]
    have hfst : ContinuousAt (fun wb : W × F => (wb.1 : X)) wa :=
      (continuous_subtype_val.comp continuous_fst).continuousAt
    have hb : Tendsto (fun wb : W × F => (e wa.2).symm wb.1.val)
        (𝓝 wa) (𝓝 (inv wa)) :=
      Filter.Tendsto.comp ((e wa.2).symm.continuousAt (htarget wa.2 wa.1)) hfst
    exact hb.congr' heq
  let G : W × F → (g ⁻¹' W) := fun wa =>
    ⟨inv wa, by
      change g ((e wa.2).symm wa.1.val) ∈ W
      rw [(hinv wa.2 wa.1).2]
      exact wa.1.property⟩
  have hGcont : Continuous G := hinv_cont.subtype_mk _
  have hleft : ∀ y, G (H y) = y := by
    intro y
    apply Subtype.ext
    change (e (idx y)).symm (g y.val) = y.val
    have hgy : g y.val = (e (idx y)) y.val := congrFun (he_eq (idx y)) y.val
    rw [hgy]
    exact (e (idx y)).left_inv (hidx y).1
  have hright : ∀ wa, H (G wa) = wa := by
    intro wa
    apply Prod.ext
    · apply Subtype.ext
      exact (hinv wa.2 wa.1).2
    · exact hidx_eq (hinv wa.2 wa.1).1
  let homeo : (g ⁻¹' W) ≃ₜ W × F :=
    { toFun := H
      invFun := G
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hHcont
      continuous_invFun := hGcont }
  exact ⟨inferInstance, W, hxW, hWopen, hWpreopen, homeo, fun _ => rfl⟩
