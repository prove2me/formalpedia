-- Prove2me | Theorems.Thm_Fpy_equiv_floatToFixed
-- name    : Fpy.equiv_floatToFixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:39:35.27096+00:00
-- url     : https://prove2.me/theorems/4325bbc1-e0b5-44e3-a0da-484103147ca3
-- title:
--   Fpy: equiv float To Fixed
-- statement:
--   **FloatToFixed**: `[C] x = round(t) ⇝ with R in n = max(logb(t) + (1 − p), exp);
--   with C' in x = round(t)`, where `C` rounds into `𝒜(p, exp, ∞)` with `p ≠ 1` and `C'`, built
--   from `n`, rounds into `𝒜(∞, n, ∞)` with `C`'s mode, for finite nonzero `t`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L440-L480
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L440-L480

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}

theorem Fpy.equiv_floatToFixed {C : Val} {c : RoundCtx} {cf : Expr (fpy decode)} {x t n : Var}
    {p : ℕ} (hC : C.rnd (fpy decode) = some c.round) (hp : c.F.p = p) (hp1 : p ≠ 1)
    (hb : c.F.b = ⊤) (hnt : n ≠ t)
    (hcf : ∀ σ (k : ℤ), σ n = some (.num (.finite k)) → ∃ C' c', DenotesAt Φ σ cf C' ∧
      C'.rnd (fpy decode) = some (RoundCtx.round c') ∧ c'.F.p = ⊤ ∧ c'.F.exp = (k : QExp) ∧
      c'.F.b = ⊤ ∧ c'.rm = c.rm)
    (hfin : ∀ σ, Γ.Holds σ → ∀ u, σ t = some (.num u) → ∃ y, u = .finite y ∧ y ≠ 0) :
    Equiv Φ {n} Γ (some C) (.assign x (.arithOp .round [.var t]))
      (.seq (.withCtx .real (.assign n (.arithOp .max
          [.arithOp .add [.arithOp .logb [.var t], .num (.finite (1 - p))],
            .num (qexpNum c.F.exp)])))
        (.withCtx cf (.assign x (.arithOp .round [.var t])))) := by sorry
