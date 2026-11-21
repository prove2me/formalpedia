-- Prove2me | solution 1 for Mpfx.Format.withBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:56.945678+00:00
-- url     : https://prove2.me/submissions/e8c28d19-9f41-4738-9b84-dbe0a3cd0607

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_subset_of_mem


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) {b b' : Bound} (h : ∀ v, boundOK b v → boundOK b' v) :
    F.withBound b ⊆ F.withBound b' :=
  subset_of_mem subset_rfl fun v hv => ⟨hv.1, hv.2.1, h v hv.2.2⟩
end Mpfx.Format
