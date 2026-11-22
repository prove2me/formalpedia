-- Prove2me | solution 1 for Fpy.DigitBound.Within.grow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:19:02.017247+00:00
-- url     : https://prove2.me/submissions/f970de9b-acd6-47d1-8875-01d0c2711c15

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_grow

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace Within
theorem _root_.solution {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ')
    {ι ι' : Asgn} (h : Agree n ι ι') {Δ' : DEnv} {a : Option DVal} (hΔ : Δ'.Below n)
    (ha : RetBelow n a) : ∀ {o : Outcome}, Within Ψ ι Δ' a o → Within (Ψ ++ Ψ') ι' Δ' a o
  | .normal _, hw => DEnv.Holds.grow hb hF h hΔ hw
  | .ret _, ⟨d, hd, hv⟩ => ⟨d, hd, hv.grow hb hF h (ha d hd)⟩
end Within
end Fpy.DigitBound
