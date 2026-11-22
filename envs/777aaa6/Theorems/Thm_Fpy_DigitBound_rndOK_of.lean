-- Prove2me | Theorems.Thm_Fpy_DigitBound_rndOK_of
-- name    : Fpy.DigitBound.rndOK_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:47.393336+00:00
-- url     : https://prove2.me/theorems/95d99cbb-0212-4eff-ab65-1be2fb5b7514
-- title:
--   Digit Bound: rnd OK of
-- statement:
--   A row whose interval is fresh, bounded by `Lr` and `Hr` on the input's
--   endpoints and joined with the overflow and special values' digits. `Lr` may
--   mention the result's most significant digit `n`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L234-L246
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L234-L246

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.rndOK_of {κ : Option SCtx} {P : Asgn → RoundCtx → Prop} {Lr Hr Lo Ho : Term}
    (hLr : Lr.Below (n + 1)) (hHr : Hr.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ P Lo Ho) (htop : ∀ ι, m.eval ι = ⊤ → Hr.eval ι = ⊤)
    (hrow : ∀ ι c (x : ℝ) (y : Mpfx.Dyadic), P ι c → x ≠ 0 → lsbOf (.finite x) = l.eval ι →
      msbOf (.finite x) = m.eval ι → RoundsFinite c.F.unbounded c.rm x y → (y : ℝ) ≠ 0 →
      msbOf (.finite (y : ℝ)) ≤ Hr.eval ι ∧
        Lr.eval (Function.update ι n (msbOf (.finite (y : ℝ)))) ≤ lsbOf (.finite (y : ℝ))) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min Lr Lo) (.max Hr Ho) ⟨hLr, hLo.mono (Nat.le_succ n)⟩ ⟨hHr, hHo⟩)
      (.var (n + 1)) (.var n) := by sorry
