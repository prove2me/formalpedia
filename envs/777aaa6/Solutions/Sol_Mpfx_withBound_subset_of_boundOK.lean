-- Prove2me | solution 1 for Mpfx.withBound_subset_of_boundOK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:52:02.5638+00:00
-- url     : https://prove2.me/submissions/0917bf4a-f90f-4532-83db-9d7b754ae8fe

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_Format_withBound_mono
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_boundOK_of_abs_le


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : Format) {B : Bound} {T : NonNegDyadic}
    (hT : Format.boundOK B T.val) : F.withBound (T : Bound) ⊆ F.withBound B :=
  Format.withBound_mono F fun _ hv =>
    boundOK_of_abs_le ((abs_coe_real_le_of_boundOK hv).trans (le_abs_self _)) hT
end Mpfx
