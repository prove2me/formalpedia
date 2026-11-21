-- Prove2me | solution 1 for Mpfx.Format.extend_one_extend_one_subset_extend_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:17.962159+00:00
-- url     : https://prove2.me/submissions/416d6112-e84c-40eb-b737-68acce3495b8

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_extend_extend

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) :
    (F.extend 1).extend 1 ⊆ F.extend 2 := by
  rw [extend_extend]
end Mpfx.Format
