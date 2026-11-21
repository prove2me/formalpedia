-- Prove2me | solution 1 for Mpfx.Format.extend_exp_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:55:04.062485+00:00
-- url     : https://prove2.me/submissions/4b3db65b-e371-4862-afd2-a648dd598227

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} (h : F.exp = ⊥) (k : ℕ) : (F.extend k).exp = ⊥ := by
  change F.exp.map _ = _; rw [h]; rfl
end Mpfx.Format
