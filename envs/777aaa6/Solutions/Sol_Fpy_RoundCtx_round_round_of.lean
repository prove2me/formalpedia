-- Prove2me | solution 1 for Fpy.RoundCtx.round_round_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:29.610958+00:00
-- url     : https://prove2.me/submissions/f84611eb-18cd-42a2-897f-c3996e28e181

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_RoundCtx_round_round_of_rnd
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_rnd_finite_of_roundsFinite
import Theorems.Thm_Mpfx_rnd_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.rnd_special



set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy
namespace RoundCtx
theorem _root_.solution {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm)
    {n : Num} (hn : ∀ x, n = .finite x → ∀ z, RoundsFinite c₂.F.unbounded c₂.rm x z →
      Format.boundOK c₂.F.b z ∧
        ∀ w, RoundsFinite c₁.F.unbounded c₁.rm z w → RoundsFinite c₁.F.unbounded c₁.rm x w) :
    c₁.round (c₂.round n) = c₁.round n := by
  refine round_round_of_rnd fun u hu => ?_
  cases n with
  | special s =>
    rw [rnd_special] at hu
    obtain rfl := RoundResult.value.inj hu
    rw [hS s, rnd_special]
  | finite x =>
    have hz := rndUnbounded_satisfies c₂.F c₂.rm x c₂.defined
    generalize rndUnbounded c₂.F c₂.rm x c₂.defined = z at hz
    obtain ⟨hb, hdr⟩ := hn x rfl z hz
    rw [rnd_finite_of_roundsFinite c₂.defined hz, if_pos hb] at hu
    obtain rfl := RoundResult.value.inj hu
    have hw := rndUnbounded_satisfies c₁.F c₁.rm (z : ℝ) c₁.defined
    rw [WithSpecial.toReal_finite, rnd_finite_of_roundsFinite c₁.defined hw,
      rnd_finite_of_roundsFinite c₁.defined (hdr _ hw)]
end RoundCtx
end Fpy
