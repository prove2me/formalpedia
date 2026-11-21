-- Prove2me | solution 1 for Mpfx.canonicalExp_expBot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:50:56.444458+00:00
-- url     : https://prove2.me/submissions/e167647b-44d8-4232-ae16-b1f77d08628e

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_canonicalExp_closed

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {p : ℕ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = ⊥)
    {v : ℝ} (hv : v ≠ 0) : F.canonicalExp v = Int.log 2 |v| + 1 - (p : ℤ) :=
  canonicalExp_closed hp hv (by rw [hexp]; exact bot_le)
end Mpfx
