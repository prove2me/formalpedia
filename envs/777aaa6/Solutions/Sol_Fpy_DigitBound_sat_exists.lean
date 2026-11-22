-- Prove2me | solution 1 for Fpy.DigitBound.sat_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:02.303822+00:00
-- url     : https://prove2.me/submissions/b838603c-2282-4f86-b951-1131d1342293

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
import Theorems.Thm_Fpy_DigitBound_sat_decode
import Theorems.Thm_Fpy_DigitBound_sat_iff

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
theorem _root_.solution (Ψ : List Con) : (∃ ι, Sat ι Ψ) ↔ ∃ M : IModel, ∀ φ ∈ encode Ψ, φ.holds M :=
  ⟨fun ⟨ι, h⟩ => ⟨_, (sat_iff ι Ψ).mp h⟩, fun ⟨M, h⟩ => ⟨_, (sat_decode M Ψ).mpr h⟩⟩
end Fpy.DigitBound
