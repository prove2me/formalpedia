-- Prove2me | Theorems.Thm_Fpy_eval_sum
-- name    : Fpy.eval_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:53.688881+00:00
-- url     : https://prove2.me/theorems/38ca8c90-4b39-4ca6-b70f-432d38cf091a
-- title:
--   Fpy: eval sum
-- statement:
--   **A-Sum**: a call to `sum` on `e : [F]` of length `L`, under a context with
--   rounding `r`, returns a value in `F_L`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sum.lean#L47-L64
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sum.lean#L47-L64

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_FormatInference_Sum
set_option autoImplicit true
open Fpy
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}

theorem Fpy.eval_sum (hA : A.Sound Φ) (hsum : Φ "sum" = some ("xs", sumBody)) {Γ : AEnv D}
    {κ : Option Val} {σ : Store} {C : Val} {r : Num → Num} {e : Expr (fpy decode)}
    {F : D.Fmt} {L : ℕ} {v : Val} (hΓ : Γ.Holds σ) (hκ : Admits κ C)
    (hr : C.rnd (fpy decode) = some r) (he : AEval A Φ Γ κ e (.list (.fmt F)))
    (hL : ∀ vs, Eval Φ σ C e (.list vs) → vs.length = L) (h : Eval Φ σ C (.call "sum" e) v) :
    Describes (.fmt (sumFmt A κ F L)) v := by sorry
