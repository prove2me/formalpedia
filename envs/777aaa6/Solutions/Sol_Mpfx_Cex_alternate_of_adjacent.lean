-- Prove2me | solution 1 for Mpfx.Cex.alternate_of_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:26:47.30362+00:00
-- url     : https://prove2.me/submissions/dc5c91a4-d7cd-46c2-b92a-1702b08848e3

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Theorems.Thm_Mpfx_ParityFormat_not_isUndefined
import Theorems.Thm_Mpfx_alternate_of_bracketing


set_option autoImplicit true
open Mpfx
open Mpfx.Cex
namespace Mpfx.Cex
theorem _root_.solution (F : ParityFormat) {u u' : Dyadic}
    (h : Adjacent F.toFiniteFormat u u') :
    (F.IsOdd u' ↔ ¬ F.IsOdd u) ∧ (¬ F.IsEven u → F.IsEven u') := by
  obtain ⟨hu, hu', hlt, hadj⟩ := h
  set x : ℝ := ((u : ℝ) + u') / 2 with hx
  have hdown : RoundsFinite F.unbounded.unbounded .toNegative x u :=
    ⟨hu, by linarith, fun v hv hvx => hadj v hv (by linarith)⟩
  have hup : RoundsFinite F.unbounded.unbounded .toPositive x u' :=
    ⟨hu', by linarith, fun v hv hxv => not_lt.mp fun hv' => by linarith [hadj v hv hv']⟩
  exact alternate_of_bracketing (F := F.unbounded) (F.not_isUndefined .toOdd) hdown hup
    (by linarith)
end Mpfx.Cex
