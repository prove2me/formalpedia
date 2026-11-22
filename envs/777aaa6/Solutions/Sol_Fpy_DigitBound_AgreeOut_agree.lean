-- Prove2me | solution 1 for Fpy.DigitBound.AgreeOut.agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:05.656495+00:00
-- url     : https://prove2.me/submissions/ae8530d2-bf06-4901-acbd-a99ea9832070

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
namespace AgreeOut
theorem _root_.solution {n₀ n₁ : ℕ} {ι ι' : Asgn} (h : AgreeOut n₀ n₁ ι ι') : Agree n₀ ι ι' :=
  fun x hx => (h x (.inl hx)).symm
end AgreeOut
end Fpy.DigitBound
