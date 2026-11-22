-- Prove2me | solution 1 for Fpy.DigitBound.opOK_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:12.765353+00:00
-- url     : https://prove2.me/submissions/05103a15-4786-401e-bb8a-0e789fe8f5e7

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr
import Theorems.Thm_Fpy_DigitBound_fresh_numIn


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy.DigitBound
theorem _root_.solution {op : ArithOp} {Is : List (Term × Term × Option Term)} {n : ℕ} {Lo Hi : Term}
    (hLo : Lo.Below n) (hHi : Hi.Below n)
    (h : ∀ ι ns u, List.Forall₂ (fun (I : Term × Term × Option Term) n => NumIn ι I.1 I.2.1 I.2.2 n)
      Is ns → op.eval ns = some u → u ≠ nan → msbOf u ≤ Hi.eval ι ∧ Lo.eval ι ≤ lsbOf u) :
    OpOK op Is n (n + 2) (bounds n Lo Hi (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1))
      (.var n) := fun ι ns u hns hop => fresh_numIn _ hHi ι u fun hu => by
  obtain ⟨h₁, h₂⟩ := h ι ns u hns hop hu
  exact ⟨h₁, by rwa [← Term.eval_congr (fun x hx => (Function.update_of_ne hx.ne _ _).symm) hLo]⟩
end Fpy.DigitBound
