-- Prove2me | solution 1 for Mpfx.mem_unbounded_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:44.335684+00:00
-- url     : https://prove2.me/submissions/54d10aac-e6e1-4718-ae55-99241bf4125b

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {d : Dyadic}
    (h : d ∈ F) : d ∈ F.unbounded :=
  ⟨h.1, h.2.1, trivial⟩
end Mpfx
