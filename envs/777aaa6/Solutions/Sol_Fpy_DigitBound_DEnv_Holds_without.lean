-- Prove2me | solution 1 for Fpy.DigitBound.DEnv.Holds.without
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:18:13.78584+00:00
-- url     : https://prove2.me/submissions/27893029-f5a1-4b97-b3f3-8ee09afd55a1

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
namespace DEnv.Holds
theorem _root_.solution {Δ : DEnv} {Ψ : List Con} {ι : Asgn} {σ : Store}
    (hσ : Δ.Holds Ψ ι σ) (X : List Var) : (Δ.without X).Holds Ψ ι σ := fun x d hx =>
  hσ x d (DEnv.without_eq_some.mp hx).2
end DEnv.Holds
end Fpy.DigitBound
