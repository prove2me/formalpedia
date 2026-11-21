-- Prove2me | solution 1 for Mpfx.canonicalExp_subnormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:53:14.152361+00:00
-- url     : https://prove2.me/submissions/1adbd816-65f1-41fc-b755-9c8083fd3dc6

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
import Theorems.Thm_Mpfx_canonicalExp_expFinite

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {p : ℕ} {emin : ℤ}
    (hp : F.p = (p : Prec)) (hexp : F.exp = (emin : QExp)) {v : ℝ} (hv : v ≠ 0)
    (h : Int.log 2 |v| + 1 - (p : ℤ) ≤ emin) : F.canonicalExp v = emin := by
  rw [canonicalExp_expFinite hp hexp hv]; exact max_eq_right h
end Mpfx
