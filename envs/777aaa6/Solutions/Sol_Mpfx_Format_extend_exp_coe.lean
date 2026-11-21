-- Prove2me | solution 1 for Mpfx.Format.extend_exp_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:49:43.604565+00:00
-- url     : https://prove2.me/submissions/554f6cb1-ec8b-4558-90d4-64634ca15ed7

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} {e : ℤ} (h : F.exp = e) (k : ℕ) :
    (F.extend k).exp = ((e - k : ℤ) : QExp) := by
  change F.exp.map _ = _; rw [h]; rfl
end Mpfx.Format
