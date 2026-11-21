-- Prove2me | solution 1 for Mpfx.mem_of_mem_unbounded_of_boundOK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:34.882199+00:00
-- url     : https://prove2.me/submissions/1e0b6d00-7608-481e-b680-39460f6f80d4

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F.unbounded) (hb : Format.boundOK F.b d) : d ∈ F :=
  ⟨h.1, h.2.1, hb⟩
end Mpfx
