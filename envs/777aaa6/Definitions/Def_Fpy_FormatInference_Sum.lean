-- Prove2me | Definitions.Def_Fpy_FormatInference_Sum
-- name    : Fpy_FormatInference_Sum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T06:07:04.006289+00:00
-- url     : https://prove2.me/theorems/67eee56f-7cdf-4b70-9cd5-c3850e6d36a2
-- title:
--   Sum
-- statement:
--   Definitions and structural lemmas for Sum, from Brett Saiki and contributors's pinned Correct double rounding and FPy analyses development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sum.lean

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Sum
set_option autoImplicit true
namespace Fpy
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
variable (A) in
/-- `F_L`: the format of the sum of `L` values in `F` under `κ`. -/
noncomputable def sumFmt (κ : Option Val) (F : D.Fmt) : ℕ → D.Fmt
  | 0 => D.ofNum (.finite 0)
  | 1 => F
  | n + 2 => A.rnd κ (A.arith .add [sumFmt κ F (n + 1), F])
end Fpy


