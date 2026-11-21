-- Prove2me | solution 1 for Mpfx.ParityFormat.not_isUndefined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:41:53.479393+00:00
-- url     : https://prove2.me/submissions/1429d62d-97c2-4682-80fa-23423e5e5291

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace ParityFormat
theorem _root_.solution (F : ParityFormat) (rm : RoundingMode) :
    ¬ F.IsUndefined rm :=
  fun ⟨hp, he, _⟩ => F.parity.elim (· hp) (· he)
end ParityFormat
end Mpfx
