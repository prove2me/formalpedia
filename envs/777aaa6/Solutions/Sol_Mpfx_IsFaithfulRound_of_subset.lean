-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:47.503736+00:00
-- url     : https://prove2.me/submissions/d38990ad-429e-4a81-a547-f6134b34e33b

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {y : Dyadic} (h : IsFaithfulRound F₂ x y) (hy : y ∈ F₁) : IsFaithfulRound F₁ x y :=
  h.imp (fun ⟨_, h₁, h₂⟩ => ⟨hy, h₁, fun v hv => h₂ v (hsub _ hv)⟩)
    (fun ⟨_, h₁, h₂⟩ => ⟨hy, h₁, fun v hv => h₂ v (hsub _ hv)⟩)
end IsFaithfulRound
end Mpfx
