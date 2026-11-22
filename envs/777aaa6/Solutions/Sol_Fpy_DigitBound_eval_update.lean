-- Prove2me | solution 1 for Fpy.DigitBound.eval_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:03.956697+00:00
-- url     : https://prove2.me/submissions/cc272b57-368c-40dc-b404-952220903e25

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr


set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
theorem _root_.solution {n : ℕ} {t : Term} (h : t.Below n) (ι : Asgn) (z : EInt) :
    t.eval (Function.update ι n z) = t.eval ι :=
  (Term.eval_congr (fun _ hx => (Function.update_of_ne hx.ne _ _).symm) h).symm
end Fpy.DigitBound
