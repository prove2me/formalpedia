-- Prove2me | solution 1 for Fpy.fpy_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:22.012465+00:00
-- url     : https://prove2.me/submissions/e0d06646-2124-4413-9478-0113d1b51e88

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy
theorem _root_.solution (u : Num) : (fpy decode).arith (show ArithOp from .round) [u] = some u := rfl
end Fpy
