-- Prove2me | solution 1 for Mpfx.Format.subset_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:49:40.260874+00:00
-- url     : https://prove2.me/submissions/91618c7c-b71d-45f2-825f-6b65dedd8388

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F₁ F₂ : Format} (hs : F₁.specials ⊆ F₂.specials)
    (h : ∀ x : Dyadic, x ∈ F₁ → x ∈ F₂) : F₁ ⊆ F₂ := ⟨h, hs⟩
end Mpfx.Format
