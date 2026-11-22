-- Prove2me | solution 1 for Fpy.DigitBound.ArithOK.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:47:40.271433+00:00
-- url     : https://prove2.me/submissions/742a9181-626f-48e6-adff-e44ac5daf4c7

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_AgreeOut_agree
import Theorems.Thm_Fpy_DigitBound_LsbAt_le
import Theorems.Thm_Fpy_DigitBound_admits_congr


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy.DigitBound
namespace ArithOK
theorem _root_.solution {κ : Option SCtx} {op : ArithOp} {Is : List (Term × Term × Option Term)}
    {n₀ n₁ n₂ : ℕ} {Ψ₁ Ψ₂ : List Con} {l m l' m' : Term} (ho : OpOK op Is n₀ n₁ Ψ₁ l m)
    (hr : RndOK decode κ l m n₁ n₂ Ψ₂ l' m') (hF₁ : Fresh n₀ n₁ Ψ₁) (hF₂ : Fresh n₁ n₂ Ψ₂)
    (hκ : CtxBelow n₀ κ) : ArithOK decode κ op Is n₀ n₂ (Ψ₁ ++ Ψ₂) l' m' := by
  intro ι ns u C r hns hop hC hr'
  obtain ⟨ι₁, a₁, s₁, h₁⟩ := ho ι ns u hns hop
  obtain ⟨ι₂, a₂, s₂, h₂⟩ := hr ι₁ u C r h₁ (admits_congr a₁.agree hκ hC) hr'
  refine ⟨ι₂, fun x hx => ?_, (Sat.congr hF₁.before a₂.agree s₁).append s₂, h₂⟩
  have := hF₁.le
  have := hF₂.le
  rw [a₂ x (by omega), a₁ x (by omega)]
end ArithOK
end Fpy.DigitBound
