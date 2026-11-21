-- Prove2me | solution 1 for Mpfx.boundOK_boundAfterNext_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:10.041783+00:00
-- url     : https://prove2.me/submissions/f3ed1987-113c-4c36-b990-e10bcc9658b8

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
section
namespace Mpfx
namespace Format
private theorem boundAfterNext_coe {F : Format} {b : NonNegDyadic} (hF : F.b = (b : Bound)) :
    ∃ h, F.boundAfterNext = ((⟨F.next b.val, h⟩ : NonNegDyadic) : Bound) := by
  unfold boundAfterNext; rw [hF]; exact ⟨_, rfl⟩
end Format
namespace FiniteFormat
end FiniteFormat
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound))
    (hN_nn : 0 ≤ ((F₁.toFormat.next b₁.val : _root_.Mpfx.Dyadic) : ℝ)) :
    Format.boundOK F₁.toFormat.boundAfterNext (F₁.toFormat.next b₁.val) := by
  obtain ⟨hnn, h_eq⟩ := Format.boundAfterNext_coe hF₁b
  rw [h_eq]
  have hN_nn_q : (0 : ℚ) ≤ ((F₁.toFormat.next b₁.val : _root_.Mpfx.Dyadic) : ℚ) := by
    exact_mod_cast hN_nn
  change |((F₁.toFormat.next b₁.val : _root_.Mpfx.Dyadic) : ℚ)|
    ≤ ((F₁.toFormat.next b₁.val : _root_.Mpfx.Dyadic) : ℚ)
  rw [abs_of_nonneg hN_nn_q]
end Mpfx
