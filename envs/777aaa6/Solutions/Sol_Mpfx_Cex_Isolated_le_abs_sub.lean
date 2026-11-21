-- Prove2me | solution 1 for Mpfx.Cex.Isolated.le_abs_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:47:27.834919+00:00
-- url     : https://prove2.me/submissions/5c4def8a-abf8-4260-8171-712d49906b77

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
namespace Isolated
theorem _root_.solution {F : FiniteFormat} {m : Dyadic} {K : ℤ} (h : Isolated F m K)
    {v : Dyadic} (hv : v ∈ F.unbounded) (hne : v ≠ m) : (2 : ℝ) ^ K ≤ |(v : ℝ) - m| :=
  not_lt.mp fun hlt => hne (h v hv hlt)
end Isolated
end Mpfx.Cex
