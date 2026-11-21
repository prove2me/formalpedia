-- Prove2me | solution 1 for Mpfx.mem_extend_one_withBound_of_mem_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:57:05.480405+00:00
-- url     : https://prove2.me/submissions/12f72873-f0f8-47ac-9fc8-ebcf326d16c0

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_self_subset_extend


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ : FiniteFormat} {d : _root_.Mpfx.Dyadic}
    (hd : d ∈ F₁.unbounded)
    (hb : Format.boundOK F₁.toFormat.boundAfterNext d) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by
  have hd' := Format.self_subset_extend F₁.toFormat.unbounded 1 d hd
  exact ⟨hd'.1, hd'.2.1, hb⟩
end Mpfx
