-- Prove2me | solution 1 for Mpfx.two_le_p_or_trivial_of_extend_two_withBound_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:50.213795+00:00
-- url     : https://prove2.me/submissions/cb6207f7-9da0-48c2-a769-5687f24af014

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_two_le_p_or_trivial_of_extend_one_withBound_subset
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
              ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : _root_.Mpfx.Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by
  have hsub' := extend_one_extend_one_withBound_subset hsub
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub' with h | htriv
  · exact Or.inl h
  · exact Or.inr fun d hd => htriv d (Format.self_subset_extend F₁.toFormat 1 d hd)
end Mpfx
