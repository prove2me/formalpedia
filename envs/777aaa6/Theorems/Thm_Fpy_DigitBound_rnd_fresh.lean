-- Prove2me | Theorems.Thm_Fpy_DigitBound_rnd_fresh
-- name    : Fpy.DigitBound.rnd_fresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:33.996059+00:00
-- url     : https://prove2.me/theorems/f0f06fcc-a8b1-4057-872e-53314b5cebf7
-- title:
--   Digit Bound: rnd fresh
-- statement:
--   One context's rounding of a value in `[l, m]` lies in a row's fresh interval.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L190-L229
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L190-L229

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.rnd_fresh {P : Asgn → RoundCtx → Prop} {Lr Hr Lo Ho : Term}
    (hLr : Lr.Below (n + 1)) (hHr : Hr.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (htop : ∀ ι, m.eval ι = ⊤ → Hr.eval ι = ⊤)
    (hrow : ∀ ι c (x : ℝ) (y : Mpfx.Dyadic), P ι c → x ≠ 0 → lsbOf (.finite x) = l.eval ι →
      msbOf (.finite x) = m.eval ι → RoundsFinite c.F.unbounded c.rm x y → (y : ℝ) ≠ 0 →
      msbOf (.finite (y : ℝ)) ≤ Hr.eval ι ∧
        Lr.eval (Function.update ι n (msbOf (.finite (y : ℝ)))) ≤ lsbOf (.finite (y : ℝ)))
    {ι : Asgn} {u : Num} {c : RoundCtx} (hu : NumIn ι l m none u) (hP : P ι c)
    (himg : ImagesIn c (Lo.eval ι) (Ho.eval ι)) :
    ∃ ι', AgreeOut n (n + 2) ι ι' ∧
      Sat ι' (bounds n (.min Lr Lo) (.max Hr Ho) ⟨hLr, hLo.mono (Nat.le_succ n)⟩ ⟨hHr, hHo⟩) ∧
      NumIn ι' (.var (n + 1)) (.var n) none (c.round u) := by sorry
