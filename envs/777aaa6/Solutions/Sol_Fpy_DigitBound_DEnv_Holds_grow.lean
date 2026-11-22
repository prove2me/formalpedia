-- Prove2me | solution 1 for Fpy.DigitBound.DEnv.Holds.grow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:17:19.624646+00:00
-- url     : https://prove2.me/submissions/47cb831f-08c8-4a5b-9835-4d8b5a6140e8

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
namespace DEnv.Holds
theorem _root_.solution {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ')
    {ι ι' : Asgn} (h : Agree n ι ι') {Δ : DEnv} {σ : Store} (hΔ : Δ.Below n)
    (hσ : Δ.Holds Ψ ι σ) : Δ.Holds (Ψ ++ Ψ') ι' σ := fun x d hx => by
  obtain ⟨v, hv, hd⟩ := hσ x d hx
  exact ⟨v, hv, hd.grow hb hF h (hΔ x d hx)⟩
end DEnv.Holds
end Fpy.DigitBound
