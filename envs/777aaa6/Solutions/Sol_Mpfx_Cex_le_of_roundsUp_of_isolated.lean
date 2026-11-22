-- Prove2me | solution 1 for Mpfx.Cex.le_of_roundsUp_of_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:02:21.716066+00:00
-- url     : https://prove2.me/submissions/bc4a7d9b-2dab-47c4-b568-ce8b20d1e172

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic

set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution {F : FiniteFormat} {m : Dyadic} {K : ℤ}
    (hK : Isolated F m K) {x : ℝ} {z : Dyadic} (hz : RoundsFinite F.unbounded .toPositive x z)
    (hx : (m : ℝ) - (2 : ℝ) ^ K < x) : (m : ℝ) ≤ z :=
  not_lt.mp fun hlt => by
    have hzx := hz.2.1
    have := hK z hz.1 (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    rw [this] at hlt
    exact lt_irrefl _ hlt
end Mpfx.Cex
