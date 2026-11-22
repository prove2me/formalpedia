-- Prove2me | solution 1 for Fpy.DigitBound.admits_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:19:11.555682+00:00
-- url     : https://prove2.me/submissions/ee568664-5fc8-405c-8a7c-0ea1bfc96eb0

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
theorem _root_.solution {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') {κ : Option SCtx} {C : Val}
    (hκ : CtxBelow n κ) (hC : ∀ K ∈ κ, K.Admits ι C) : ∀ K ∈ κ, K.Admits ι' C :=
  fun K hK => (hC K hK).congr h (hκ K hK)
end Fpy.DigitBound
