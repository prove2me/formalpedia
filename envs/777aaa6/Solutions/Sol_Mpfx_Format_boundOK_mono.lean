-- Prove2me | solution 1 for Mpfx.Format.boundOK_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:53:35.933953+00:00
-- url     : https://prove2.me/submissions/d0fb58a2-9aeb-4d50-851c-25f46b6e1aa4

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {b₁ b₂ : Bound} (h : b₁ ≤ b₂) {x : Dyadic} :
    boundOK b₁ x → boundOK b₂ x := by
  match b₁, b₂ with
  | _, ⊤ => intro _; trivial
  | ⊤, (_ : NonNegDyadic) => exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
  | (d₁ : NonNegDyadic), (d₂ : NonNegDyadic) =>
    intro hx
    have h12 : d₁ ≤ d₂ := WithTop.coe_le_coe.mp h
    have hd : ((d₁.val : Dyadic) : ℚ) ≤ ((d₂.val : Dyadic) : ℚ) := by
      exact_mod_cast h12
    exact le_trans hx hd
end Mpfx.Format
