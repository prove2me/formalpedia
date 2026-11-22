-- Prove2me | solution 1 for Mpfx.extend_one_subset_of_withBound_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:04.512193+00:00
-- url     : https://prove2.me/submissions/fb8f3e05-036a-4272-a6a8-d4a56a02dcba

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_withBound_mono
import Theorems.Thm_Mpfx_boundOK_boundAfterNext_of_boundOK

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    (F₁.extend 1).toFormat ⊆ F₂.toFormat :=
  (Format.withBound_mono _ (b := F₁.b) fun _ => boundOK_boundAfterNext_of_boundOK).trans hsub
end Mpfx
