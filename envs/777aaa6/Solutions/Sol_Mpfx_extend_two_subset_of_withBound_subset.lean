-- Prove2me | solution 1 for Mpfx.extend_two_subset_of_withBound_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:31:18.181448+00:00
-- url     : https://prove2.me/submissions/3ab95260-6d65-48ee-ba96-55fdc0639e36

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_extend_one_subset_of_withBound_subset
import Theorems.Thm_Mpfx_Format_extend_extend

section
namespace Mpfx
namespace Format
end Format
namespace FiniteFormat
end FiniteFormat
private theorem extend_one_extend_one_toFormat (F : FiniteFormat) :
    ((F.extend 1).extend 1).toFormat = (F.extend 2).toFormat :=
  Format.extend_extend F.toFormat 1 1
private theorem extend_one_extend_one_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (((F₁.extend 1).extend 1).toFormat.withBound
      (F₁.extend 1).toFormat.boundAfterNext) ⊆ F₂.toFormat := by
  rwa [extend_one_extend_one_toFormat]
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (F₁.extend 2).toFormat ⊆ F₂.toFormat := by
  have h := extend_one_subset_of_withBound_subset (extend_one_extend_one_withBound_subset hsub)
  rwa [extend_one_extend_one_toFormat] at h
end Mpfx
