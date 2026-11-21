-- Prove2me | solution 1 for Fpy.Store.Agree.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:04.219618+00:00
-- url     : https://prove2.me/submissions/e364e346-7b9b-42c7-b592-6c46df0c2021

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic

set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {X : Set Var}
namespace Fpy
namespace Store.Agree
theorem _root_.solution {Y : Set Var} {σ σ' : Store} (h : σ.Agree X σ') (hXY : X ⊆ Y) :
    σ.Agree Y σ' := fun x hx => h x fun h' => hx (hXY h')
end Store.Agree
end Fpy
