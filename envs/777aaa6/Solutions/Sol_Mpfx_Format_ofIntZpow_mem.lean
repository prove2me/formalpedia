-- Prove2me | solution 1 for Mpfx.Format.ofIntZpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:56.388294+00:00
-- url     : https://prove2.me/submissions/b9e66991-a681-4143-9fb1-14048bdfd307

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow


set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} {c k : ℤ}
    (hp : Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow c k))
    (he : F.exp ≤ (k : QExp)) (hb : boundOK F.b (Dyadic.ofIntZpow c k)) :
    Dyadic.ofIntZpow c k ∈ F :=
  ⟨hp, Dyadic.quantumAtLeast_ofIntZpow he, hb⟩
end Mpfx.Format
