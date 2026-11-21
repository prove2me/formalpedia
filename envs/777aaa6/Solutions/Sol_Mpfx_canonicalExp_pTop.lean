-- Prove2me | solution 1 for Mpfx.canonicalExp_pTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:43.673096+00:00
-- url     : https://prove2.me/submissions/5fe578d6-29fc-4743-a216-6871a9670c0e

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {emin : ℤ}
    (hp : F.p = ⊤) (hexp : F.exp = (emin : QExp)) (v : ℝ) : F.canonicalExp v = emin := by
  unfold FiniteFormat.canonicalExp; rw [hp, hexp]
end Mpfx
