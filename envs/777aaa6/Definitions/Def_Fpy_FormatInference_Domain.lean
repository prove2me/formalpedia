-- Prove2me | Definitions.Def_Fpy_FormatInference_Domain
-- name    : Fpy_FormatInference_Domain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:09:10.175192+00:00
-- url     : https://prove2.me/theorems/b7c34f3a-1ecd-4d91-b311-b556ee890f26
-- title:
--   Domain
-- statement:
--   Definitions and structural lemmas for Domain, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Domain.lean

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_containsPrec
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_rnd_special
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundAfterNext_top
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rnd_special


set_option autoImplicit true
namespace Fpy
open Mpfx
def _root_.Mpfx.Format.reals (F : Format) : Set Num := {n | ∃ v ∈ F.values, v.toReal = n}
noncomputable def fmtJoin (F₁ F₂ : Format) : Format where
  p := max F₁.p F₂.p
  exp := min F₁.exp F₂.exp
  b := max F₁.b F₂.b
  specials := F₁.specials ∪ F₂.specials
theorem _root_.Mpfx.Format.reals_mono {F G : Format} (h : F ⊆ G) {n : Num} (hn : n ∈ F.reals) :
    n ∈ G.reals := by
  obtain ⟨v, hv, rfl⟩ := hn
  refine ⟨v, ?_, rfl⟩
  cases v with
  | finite d => exact h d hv
  | special s => exact h.specials hv
theorem reals_fmtJoin_left {F₁ : Format} {n : Num} (h : n ∈ F₁.reals) (F₂ : Format) :
    n ∈ (fmtJoin F₁ F₂).reals :=
  Format.reals_mono (Format.containsPrec le_sup_left inf_le_left le_sup_left
    Set.subset_union_left) h
theorem reals_fmtJoin_right (F₁ : Format) {F₂ : Format} {n : Num} (h : n ∈ F₂.reals) :
    n ∈ (fmtJoin F₁ F₂).reals :=
  Format.reals_mono (Format.containsPrec le_sup_right inf_le_right le_sup_right
    Set.subset_union_right) h
inductive Fmt where
  | set (S : Finset Num)
  | abs (F : Format)
  | top
def Fmt.γ : Fmt → Set Num
  | .set S => ↑S
  | .abs F => F.reals
  | .top => Set.univ
structure Ceiling where
  ceil : Finset Num → Option Format
  sound : ∀ {S F}, ceil S = some F → ∀ n ∈ S, n ∈ F.reals
open Classical in
/-- The join of Figure 4. -/
noncomputable def Fmt.join (c : Ceiling) : Fmt → Fmt → Fmt
  | .set S₁, .set S₂ => .set (S₁ ∪ S₂)
  | .set S, .abs F | .abs F, .set S =>
      if ↑S ⊆ F.reals then .abs F else (c.ceil S).elim .top (fun F' => .abs (fmtJoin F' F))
  | .abs F₁, .abs F₂ => .abs (fmtJoin F₁ F₂)
  | _, _ => .top
open Classical in
theorem Fmt.mem_join_set {c : Ceiling} {S : Finset Num} {F : Format} {n : Num}
    (h : n ∈ (Fmt.set S).γ ∨ n ∈ (Fmt.abs F).γ) :
    n ∈ ((if ↑S ⊆ F.reals then Fmt.abs F
      else (c.ceil S).elim .top (fun F' => .abs (fmtJoin F' F))) : Fmt).γ := by
  split
  · next hS => exact h.elim (fun h => hS h) id
  · cases hc : c.ceil S with
    | none => trivial
    | some F' =>
      rcases h with h | h
      · exact reals_fmtJoin_left (c.sound hc n h) F
      · exact reals_fmtJoin_right F' h
theorem Fmt.mem_join_left {c : Ceiling} {F₁ F₂ : Fmt} {n : Num} (h : n ∈ F₁.γ) :
    n ∈ (Fmt.join c F₁ F₂).γ := by
  cases F₁ <;> cases F₂ <;> simp only [Fmt.join]
  all_goals first
    | trivial
    | exact Fmt.mem_join_set (Or.inl h)
    | exact Fmt.mem_join_set (Or.inr h)
    | exact Finset.mem_union_left _ h
    | exact reals_fmtJoin_left h _
theorem Fmt.mem_join_right {c : Ceiling} {F₁ F₂ : Fmt} {n : Num} (h : n ∈ F₂.γ) :
    n ∈ (Fmt.join c F₁ F₂).γ := by
  cases F₁ <;> cases F₂ <;> simp only [Fmt.join]
  all_goals first
    | trivial
    | exact Fmt.mem_join_set (Or.inl h)
    | exact Fmt.mem_join_set (Or.inr h)
    | exact Finset.mem_union_right _ h
    | exact reals_fmtJoin_right _ h
open Classical in
/-- The format domain of Figure 4, for a choice of `⌈S⌉`. The containment check
is exact. -/
noncomputable def Fmt.domain (c : Ceiling) : FormatDomain where
  Fmt := Fmt
  γ := Fmt.γ
  top := .top
  bot := .set ∅
  join := Fmt.join c
  sub F₁ F₂ := decide (F₁.γ ⊆ F₂.γ)
  ofNum n := .set {n}
  mem_top _ := trivial
  mem_join_left := Fmt.mem_join_left
  mem_join_right := Fmt.mem_join_right
  sub_sound h := of_decide_eq_true h
  mem_ofNum _ := Finset.mem_singleton_self _
open Classical in
/-- `F_C` for an Mpfx context: its own format, when its special map fixes
the format's specials. Other contexts are not understood. -/
noncomputable def fpyCtxFmt (decode : List (Label × Val) → Option RoundCtx) : Val → Option Fmt
  | .ctx fs => (decode fs).bind fun c =>
      if ∀ s ∈ c.F.specials, c.S.map s = .special s then some (.abs c.F.toFormat) else none
  | _ => none
end Fpy


