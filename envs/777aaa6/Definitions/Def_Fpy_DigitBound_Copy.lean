-- Prove2me | Definitions.Def_Fpy_DigitBound_Copy
-- name    : Fpy_DigitBound_Copy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:18:37.930623+00:00
-- url     : https://prove2.me/theorems/9b7da49c-c028-4890-898a-88283720fff6
-- title:
--   Copy
-- statement:
--   Definitions and structural lemmas for Copy, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean

import Definitions.Def_Fpy_DigitBound_Basic
import Theorems.Thm_Fpy_DigitBound_Con_dep
import Theorems.Thm_Fpy_DigitBound_numOfE_bot
import Theorems.Thm_Fpy_DigitBound_numOfE_coe
import Theorems.Thm_Fpy_DigitBound_numOfE_top
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
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg
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
attribute [local simp] Fpy.DigitBound.numOfE_bot
attribute [local simp] Fpy.DigitBound.numOfE_coe
attribute [local simp] Fpy.DigitBound.numOfE_top
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
namespace Fpy.DigitBound
def shift (a b n x : ℕ) : ℕ := if a ≤ x ∧ x < b then x - a + n else x
def Term.rename (f : ℕ → ℕ) : Term → Term
  | .const z => .const z
  | .var x => .var (f x)
  | .add s t => .add (s.rename f) (t.rename f)
  | .neg t => .neg (t.rename f)
  | .smul c t => .smul c (t.rename f)
  | .max s t => .max (s.rename f) (t.rename f)
  | .min s t => .min (s.rename f) (t.rename f)
theorem Term.eval_rename (f : ℕ → ℕ) (ι : Asgn) :
    ∀ t : Term, (t.rename f).eval ι = t.eval (ι ∘ f) := fun
  | .const _ | .var _ => rfl
  | .add s t | .max s t | .min s t => by
    simp only [Term.rename, Term.eval, Term.eval_rename f ι s, Term.eval_rename f ι t]
  | .neg t | .smul _ t => by simp only [Term.rename, Term.eval, Term.eval_rename f ι t]
theorem Term.Below.rename {f : ℕ → ℕ} {k k' : ℕ} (hf : ∀ x < k, f x < k') :
    ∀ {t : Term}, t.Below k → (t.rename f).Below k' := fun {t} ht => match t, ht with
  | .const _, _ => trivial
  | .var x, hx => hf x hx
  | .add _ _, ⟨hs, ht⟩ | .max _ _, ⟨hs, ht⟩ | .min _ _, ⟨hs, ht⟩ =>
    ⟨Term.Below.rename hf hs, Term.Below.rename hf ht⟩
  | .neg t, ht => Term.Below.rename (t := t) hf ht
  | .smul _ t, ht => Term.Below.rename (t := t) hf ht
def Atom.rename (f : ℕ → ℕ) (a : Atom) : Atom := ⟨a.lhs.rename f, a.rhs.rename f⟩
theorem Atom.holds_rename (f : ℕ → ℕ) (ι : Asgn) (a : Atom) :
    (a.rename f).Holds ι ↔ a.Holds (ι ∘ f) := by
  simp only [Atom.Holds, Atom.rename, Term.eval_rename]
def Con.copy (c : Con) (a b n : ℕ) (hc : a ≤ c.head ∧ c.head < b) (han : a ≤ n) : Con where
  head := c.head - a + n
  atoms := c.atoms.map (Atom.rename (shift a b n))
  below e ha := by
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    have hf : ∀ x < c.head + 1, shift a b n x < c.head - a + n + 1 := fun x hx => by
      unfold shift; split_ifs <;> omega
    exact ⟨(c.below a₀ ha₀).1.rename hf, (c.below a₀ ha₀).2.rename hf⟩
  sat ι := by
    obtain ⟨z, hz⟩ := c.sat (ι ∘ shift a b n)
    refine ⟨z, fun e ha => ?_⟩
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    refine (Atom.holds_rename _ _ _).mpr (c.dep (ι := Function.update (ι ∘ shift a b n) c.head z)
      (fun x hx => ?_) hz a₀ ha₀)
    simp only [Function.comp_apply, Function.update_apply]
    unfold shift
    split_ifs <;> first | rfl | omega
def copyCons (Ψ : List Con) (a b n : ℕ) (han : a ≤ n) : List Con :=
  Ψ.filterMap fun c => if h : a ≤ c.head ∧ c.head < b then some (c.copy a b n h han) else none
end Fpy.DigitBound


