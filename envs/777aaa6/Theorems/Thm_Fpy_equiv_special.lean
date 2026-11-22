-- Prove2me | Theorems.Thm_Fpy_equiv_special
-- name    : Fpy.equiv_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:39:01.288079+00:00
-- url     : https://prove2.me/theorems/7a96e9d5-09c0-4e8d-987a-5c0f271abe15
-- title:
--   Fpy: equiv special
-- statement:
--   **Special**: `[C] x = round(t) ⇝ if isnan(t) then x = C(NaN) elif t == −∞ then
--   x = C(−∞) elif t == +∞ then x = C(+∞) elif t == 0 then x = 0 else x = round(t)`, for a
--   context whose rounding function `r` fixes `0` (every Mpfx context, `RoundCtx.round_zero`).
--   Any branch may be omitted (`kn`, `kneg`, `kpos`, `kz` false).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L356-L372
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L356-L372

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.equiv_special {C : Val} {r : Num → Num} {x t : Var}
    (hr : C.rnd (fpy decode) = some r) (h0 : r (.finite 0) = .finite 0)
    (kn kneg kpos kz : Bool) :
    Equiv Φ X Γ (some C) (.assign x (.arithOp .round [.var t]))
      (nanBranch r kn x t
        (eqBranch kneg x t (.special (.inf true)) (r (.special (.inf true)))
        (eqBranch kpos x t (.special (.inf false)) (r (.special (.inf false)))
        (eqBranch kz x t (.finite 0) (.finite 0) (.assign x (.arithOp .round [.var t])))))) := by sorry
