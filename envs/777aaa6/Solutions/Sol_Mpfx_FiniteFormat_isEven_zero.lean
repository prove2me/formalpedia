-- Prove2me | solution 1 for Mpfx.FiniteFormat.isEven_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:04:53.907264+00:00
-- url     : https://prove2.me/submissions/f511565f-0973-435a-bdba-e58871d2023e

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_ne_zero
import Theorems.Thm_Mpfx_Dyadic_IsRepresentableAtP_ne_zero
import Theorems.Thm_Mpfx_FiniteFormat_zero_mem
import Theorems.Thm_Mpfx_Format_zero_mem


set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) : IsEven F 0 :=
  ⟨F.unbounded.zero_mem, fun h => h.ne_zero rfl⟩
end Mpfx.FiniteFormat
