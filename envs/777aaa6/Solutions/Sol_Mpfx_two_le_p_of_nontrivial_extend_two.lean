-- Prove2me | solution 1 for Mpfx.two_le_p_of_nontrivial_extend_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:03:14.611841+00:00
-- url     : https://prove2.me/submissions/21d26a9b-713a-4240-bc9b-488c3cea708c

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_two_le_p_of_nontrivial
import Theorems.Thm_Mpfx_Format_extend_extend
import Theorems.Thm_Mpfx_Format_self_subset_extend

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
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) : ((2 : ℕ) : Prec) ≤ F₂.p :=
  have ⟨d, hd, hne⟩ := hnt
  two_le_p_of_nontrivial (extend_one_extend_one_withBound_subset hsub)
    ⟨d, Format.self_subset_extend _ 1 d hd, hne⟩
end Mpfx
