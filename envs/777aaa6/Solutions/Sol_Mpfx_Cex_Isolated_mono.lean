-- Prove2me | solution 1 for Mpfx.Cex.Isolated.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:58:31.901298+00:00
-- url     : https://prove2.me/submissions/a64bdc42-3ca9-464e-b1aa-278ac137830a

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
namespace Isolated
theorem _root_.solution {F : FiniteFormat} {m : Dyadic} {K K' : ℤ} (h : Isolated F m K)
    (hK : K' ≤ K) : Isolated F m K' :=
  fun v hv hlt => h v hv (hlt.trans_le (zpow_le_zpow_right₀ (by norm_num) hK))
end Isolated
end Mpfx.Cex
