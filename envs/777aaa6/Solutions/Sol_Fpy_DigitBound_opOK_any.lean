-- Prove2me | solution 1 for Fpy.DigitBound.opOK_any
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:48:33.588118+00:00
-- url     : https://prove2.me/submissions/da488608-6e55-4fd8-aedc-92f09032bd05

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_opOK_of

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
namespace Fpy.DigitBound
theorem _root_.solution {op : ArithOp} {Is : List (Term × Term × Option Term)} :
    OpOK op Is n (n + 2) (bounds n (.const ⊥) (.const ⊤) trivial trivial) (.var (n + 1))
      (.var n) :=
  opOK_of (Lo := .const ⊥) (Hi := .const ⊤) trivial trivial fun _ _ _ _ _ _ => ⟨le_top, bot_le⟩
end Fpy.DigitBound
