-- Prove2me | solution 1 for Mpfx.FiniteFormat.p_ne_one_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:58.941174+00:00
-- url     : https://prove2.me/submissions/79e51dc0-b78f-45c0-aa39-4bdbcdd5e131

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution {F : FiniteFormat} (hp : ((2 : ℕ) : Prec) ≤ F.p) :
    F.p ≠ ((1 : ℕ) : Prec) := fun h1 => by
  rw [h1] at hp; exact absurd (ENat.coe_le_coe.mp hp : (2 : ℕ) ≤ 1) (by norm_num)
end Mpfx.FiniteFormat
