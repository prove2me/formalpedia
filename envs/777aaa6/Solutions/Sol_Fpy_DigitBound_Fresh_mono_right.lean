-- Prove2me | solution 1 for Fpy.DigitBound.Fresh.mono_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:20:37.001174+00:00
-- url     : https://prove2.me/submissions/e8d140e3-41af-4d8f-b7d5-148821e8a3cf

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
namespace Fresh
theorem _root_.solution {n₀ n₁ n₂ : ℕ} {Ψ : List Con} (h : Fresh n₀ n₁ Ψ) (h₁₂ : n₁ ≤ n₂) :
    Fresh n₀ n₂ Ψ :=
  ⟨h.1.trans h₁₂, h.2.1, fun c hc => ⟨(h.2.2 c hc).1, lt_of_lt_of_le (h.2.2 c hc).2 h₁₂⟩⟩
end Fresh
end Fpy.DigitBound
