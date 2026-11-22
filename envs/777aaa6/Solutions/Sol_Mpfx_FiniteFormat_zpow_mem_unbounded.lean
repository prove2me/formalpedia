-- Prove2me | solution 1 for Mpfx.FiniteFormat.zpow_mem_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:47.262652+00:00
-- url     : https://prove2.me/submissions/5fe11e21-236d-48a0-acbf-e7bcbd30fd91

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace FiniteFormat
theorem _root_.solution (F : FiniteFormat) {j : ℤ}
    (hj : F.exp ≤ (j : QExp)) : Dyadic.ofIntZpow 1 j ∈ F.unbounded :=
  ⟨precisionAtMost_one_zpow F.pos j, Dyadic.quantumAtLeast_ofIntZpow hj, trivial⟩
end FiniteFormat
end Mpfx
