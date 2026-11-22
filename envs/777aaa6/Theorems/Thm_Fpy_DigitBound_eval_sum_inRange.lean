-- Prove2me | Theorems.Thm_Fpy_DigitBound_eval_sum_inRange
-- name    : Fpy.DigitBound.eval_sum_inRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:45:22.498413+00:00
-- url     : https://prove2.me/theorems/1bfad5b3-1717-4724-b6a6-e56e6fd0881e
-- title:
--   Digit Bound: eval sum in Range
-- statement:
--   **D-Sum**: under `R`, a call to `sum` on `L ≥ 1` numbers with digits in
--   `[lo, hi]` returns a number with digits in `[lo, hi + ⌈log₂ L⌉]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L124-L139
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L124-L139

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}

theorem Fpy.DigitBound.eval_sum_inRange (hsum : Φ "sum" = some ("xs", sumBody)) {σ : Store}
    {e : Expr (fpy decode)} {lo hi : EInt} {L : ℕ} {v : Val} (hL : 1 ≤ L)
    (he : ∀ v₀, Eval Φ σ .real e v₀ →
      ∃ vs, v₀ = .list vs ∧ vs.length = L ∧ ∀ w ∈ vs, ∃ u, w = .num u ∧ InRange lo hi u)
    (h : Eval Φ σ .real (.call "sum" e) v) :
    ∃ u, v = .num u ∧ InRange lo (hi + ((Nat.clog 2 L : ℕ) : ℤ)) u := by sorry
