-- Prove2me | solution 1 for Mpfx.Format.containsPrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:43.922176+00:00
-- url     : https://prove2.me/submissions/328cb071-716b-455d-a36c-1ecf27fc2590

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_boundOK_mono
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F₁ F₂ : Format}
    (hp : F₁.p ≤ F₂.p) (he : F₂.exp ≤ F₁.exp) (hb : F₁.b ≤ F₂.b)
    (hs : F₁.specials ⊆ F₂.specials) : F₁ ⊆ F₂ := by
  refine ⟨fun x hx => ?_, hs⟩
  obtain ⟨hpx, hex, hbx⟩ := hx
  exact ⟨Dyadic.precisionAtMost_mono hp hpx,
         Dyadic.quantumAtLeast_anti he hex,
         boundOK_mono hb hbx⟩
end Mpfx.Format
