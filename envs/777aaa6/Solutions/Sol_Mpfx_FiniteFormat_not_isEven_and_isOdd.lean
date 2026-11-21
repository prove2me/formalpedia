-- Prove2me | solution 1 for Mpfx.FiniteFormat.not_isEven_and_isOdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:44:31.814177+00:00
-- url     : https://prove2.me/submissions/03fbb579-7b1d-4be4-b497-abffa0032643

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} {y : Dyadic}
    (h_even : F.IsEven y) (h_odd : F.IsOdd y) : False :=
  h_even.2 h_odd
end Mpfx.FiniteFormat
