-- Prove2me | Theorems.Thm_Fpy_equiv_rescale
-- name    : Fpy.equiv_rescale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:46:36.963444+00:00
-- url     : https://prove2.me/theorems/d6c9da71-5f3d-4d05-b731-e56235c32109
-- title:
--   Fpy: equiv rescale
-- statement:
--   **Rescale**: `[C] x = round(t) ⇝ with R in u = 2⁻ᵏ × t; with C₀ in m = round(u);
--   with R in x = 2ᵏ × m`, where `C₀` is `C` scaled by `2⁻ᵏ` (`RoundCtx.Scaled`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L484-L515
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L484-L515

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.equiv_rescale {C C₀ : Val} {c c₀ : RoundCtx} {ce : Expr (fpy decode)} {x t u m : Var}
    {k : ℤ} (hC : C.rnd (fpy decode) = some c.round) (hce : Denotes Φ ce C₀)
    (hC₀ : C₀.rnd (fpy decode) = some c₀.round) (hsc : c.Scaled c₀ k) :
    Equiv Φ {u, m} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx .real (.assign u (.arithOp .mul [.num (.finite (2 ^ (-k))), .var t])))
        (.seq (.withCtx ce (.assign m (.arithOp .round [.var u])))
          (.withCtx .real (.assign x (.arithOp .mul [.num (.finite (2 ^ k)), .var m]))))) := by sorry
