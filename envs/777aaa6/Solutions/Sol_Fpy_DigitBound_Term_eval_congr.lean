-- Prove2me | solution 1 for Fpy.DigitBound.Term.eval_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:10:50.520811+00:00
-- url     : https://prove2.me/submissions/f70a1d57-45a8-4a8a-af50-b4ef476e2a09

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
namespace Term
theorem _root_.solution {n : ℕ} {ι ι' : Asgn} (h : ∀ x < n, ι x = ι' x) :
    ∀ {t : Term}, t.Below n → t.eval ι = t.eval ι'
  | .const _, _ => rfl
  | .var x, hx => h x hx
  | .add _ _, ⟨ha, hb⟩ => congrArg₂ (· + ·) (solution h ha) (solution h hb)
  | .neg _, ha => congrArg negE (solution h ha)
  | .smul c _, ha => congrArg (smulE c) (solution h ha)
  | .max _ _, ⟨ha, hb⟩ => congrArg₂ Max.max (solution h ha) (solution h hb)
  | .min _ _, ⟨ha, hb⟩ => congrArg₂ Min.min (solution h ha) (solution h hb)
end Term
end Fpy.DigitBound
