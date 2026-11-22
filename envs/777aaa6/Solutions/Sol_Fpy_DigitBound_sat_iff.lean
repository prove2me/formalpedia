-- Prove2me | solution 1 for Fpy.DigitBound.sat_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:49:59.441174+00:00
-- url     : https://prove2.me/submissions/4570c210-1e47-4127-b01a-85c4818837fa

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
import Theorems.Thm_Fpy_DigitBound_decode_ofAsgn
import Theorems.Thm_Fpy_DigitBound_sat_decode

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
theorem _root_.solution (ι : Asgn) (Ψ : List Con) :
    Sat ι Ψ ↔ ∀ φ ∈ encode Ψ, φ.holds (IModel.ofAsgn ι) := by
  rw [← sat_decode, decode_ofAsgn]
end Fpy.DigitBound
