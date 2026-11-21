-- Prove2me | solution 1 for Mpfx.not_isUndefined_of_two_le_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:42:07.459902+00:00
-- url     : https://prove2.me/submissions/002c6d8e-110e-45da-86f2-286caace202c

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode}
    (hp : ((2 : ℕ) : Prec) ≤ F.p) : ¬ F.IsUndefined rm := by
  rintro ⟨h1, -, -⟩
  rw [h1] at hp
  have : (2 : ℕ) ≤ 1 := ENat.coe_le_coe.mp hp
  omega
end Mpfx
