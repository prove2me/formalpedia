-- Prove2me | solution 1 for Mpfx.two_le_p_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:48.820511+00:00
-- url     : https://prove2.me/submissions/9659c181-82be-47eb-825e-e1ded3fe131a

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_two_le_p_or_trivial_of_extend_one_withBound_subset
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) : ((2 : ℕ) : Prec) ≤ F₂.p := by
  rcases two_le_p_or_trivial_of_extend_one_withBound_subset hsub with h | htriv
  · exact h
  · obtain ⟨d, hd, hne⟩ := hnt
    exact absurd (eq_zero_of_coe_real_zero (htriv d hd)) hne
end Mpfx
