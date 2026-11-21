-- Prove2me | solution 1 for Mpfx.Format.bound_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:21.494535+00:00
-- url     : https://prove2.me/submissions/9dc76e5e-1b40-434c-8b16-2cf64df1503c

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} (hb : BoundRep F) {bv : NonNegDyadic}
    (hF : F.b = (bv : Bound)) : bv.val ∈ F := by
  obtain ⟨hp, hq, -⟩ := hb bv hF
  refine ⟨hp, hq, ?_⟩
  rw [hF]
  change |((bv.val : Dyadic) : ℚ)| ≤ ((bv.val : Dyadic) : ℚ)
  rw [abs_of_nonneg bv.property]
end Mpfx.Format
