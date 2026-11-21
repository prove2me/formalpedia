-- Prove2me | solution 1 for Mpfx.bound_top_of_withBound_top_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:55:57.986825+00:00
-- url     : https://prove2.me/submissions/8ca7462a-000a-41b0-90bc-17f662f725f0

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_b_top_of_subset


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound ⊤) ⊆ F₂.toFormat) : F₂.b = ⊤ :=
  Format.b_top_of_subset (F₁ := F₁.toFormat.withBound ⊤) F₁.pos rfl hsub
end Mpfx
