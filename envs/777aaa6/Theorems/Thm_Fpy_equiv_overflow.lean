-- Prove2me | Theorems.Thm_Fpy_equiv_overflow
-- name    : Fpy.equiv_overflow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:39:32.850064+00:00
-- url     : https://prove2.me/theorems/b55cc4c8-0003-467b-9522-a9e06f52880b
-- title:
--   Fpy: equiv overflow
-- statement:
--   **Overflow**: `[C] x = round(t) ⇝ if t ⋈⁺ τ⁺ then x = ovf(+) elif t ⋈⁻ τ⁻ then
--   x = ovf(−) else with C' in x = round(t)`, where `C` overflows exactly where a test holds
--   (`hτ`, so `τ±` depend only on `C`'s format and mode), `C'` rounds into `C`'s format without
--   its bound, and `t` is finite. Each `⋈` is `<` or `≤` (`sp`, `sn`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L380-L415
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L380-L415

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.equiv_overflow {C C' : Val} {c c' : RoundCtx} {ce : Expr (fpy decode)} {x t : Var}
    {sp sn : Bool} {τp τn : ℝ} (hC : C.rnd (fpy decode) = some c.round) (hce : Denotes Φ ce C')
    (hC' : C'.rnd (fpy decode) = some c'.round) (hF : c'.F = c.F.unbounded) (hrm : c'.rm = c.rm)
    (hτp : 0 ≤ τp) (hτn : τn < 0)
    (hτ : ∀ y, Overflows c.F c.rm y ↔
      numCmp sp (.finite τp) (.finite y) = true ∨ numCmp sn (.finite y) (.finite τn) = true)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y) :
    Equiv Φ X Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.ite (.exactOp (cmpOp sp) [.num (.finite τp), .var t])
        (.assign x (.num (c.O.map false).toReal))
        (.ite (.exactOp (cmpOp sn) [.var t, .num (.finite τn)])
          (.assign x (.num (c.O.map true).toReal))
          (.withCtx ce (.assign x (.arithOp .round [.var t]))))) := by sorry
