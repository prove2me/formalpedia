-- Prove2me | solution 1 for Mpfx.FiniteFormat.isOdd_iff_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:11:04.266034+00:00
-- url     : https://prove2.me/submissions/e481a409-de65-46be-8337-fa4c9e9b285a

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_isRepresentableAtP_numDigits_iff

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (y : Dyadic) :
    F.IsOdd y ↔ (y : ℝ) ≠ 0 ∧ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧
      if F.p = ((1 : ℕ) : Prec) then
        Odd (F.canonicalExp y - WithBot.unbotD 0 F.exp + 1) else Odd c := by
  constructor
  · rintro ⟨c, e, hrep, hpar⟩
    obtain ⟨hy0, rfl, hy⟩ := F.isRepresentableAtP_numDigits_iff.mp hrep
    exact ⟨hy0, c, hy, hpar⟩
  · rintro ⟨hy0, c, hy, hpar⟩
    exact ⟨c, _, F.isRepresentableAtP_numDigits_iff.mpr ⟨hy0, rfl, hy⟩, hpar⟩
end Mpfx.FiniteFormat
