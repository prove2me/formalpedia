-- Prove2me | solution 1 for Fpy.DigitBound.mem_copyCons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:21:27.874543+00:00
-- url     : https://prove2.me/submissions/bcfd1ec7-badd-4f7c-ba31-aad5848f49bb

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy

set_option autoImplicit true
open Fpy Fpy.DigitBound
namespace Fpy.DigitBound
theorem _root_.solution {Ψ : List Con} {a b n : ℕ} {han : a ≤ n} {c' : Con}
    (h : c' ∈ copyCons Ψ a b n han) :
    ∃ c ∈ Ψ, ∃ hc : a ≤ c.head ∧ c.head < b, c' = c.copy a b n hc han := by
  obtain ⟨c, hc, h⟩ := List.mem_filterMap.mp h
  split_ifs at h with hc'
  exact ⟨c, hc, hc', (Option.some.inj h).symm⟩
end Fpy.DigitBound
