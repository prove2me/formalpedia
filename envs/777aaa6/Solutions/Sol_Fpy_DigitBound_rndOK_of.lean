-- Prove2me | solution 1 for Fpy.DigitBound.rndOK_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:42:20.800473+00:00
-- url     : https://prove2.me/submissions/64ed506d-a071-445c-a737-479d35446cc2

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Fpy_DigitBound_rnd_fresh

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
namespace Fpy.DigitBound
theorem _root_.solution {κ : Option SCtx} {P : Asgn → RoundCtx → Prop} {Lr Hr Lo Ho : Term}
    (hLr : Lr.Below (n + 1)) (hHr : Hr.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ P Lo Ho) (htop : ∀ ι, m.eval ι = ⊤ → Hr.eval ι = ⊤)
    (hrow : ∀ ι c (x : ℝ) (y : Mpfx.Dyadic), P ι c → x ≠ 0 → lsbOf (.finite x) = l.eval ι →
      msbOf (.finite x) = m.eval ι → RoundsFinite c.F.unbounded c.rm x y → (y : ℝ) ≠ 0 →
      msbOf (.finite (y : ℝ)) ≤ Hr.eval ι ∧
        Lr.eval (Function.update ι n (msbOf (.finite (y : ℝ)))) ≤ lsbOf (.finite (y : ℝ))) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min Lr Lo) (.max Hr Ho) ⟨hLr, hLo.mono (Nat.le_succ n)⟩ ⟨hHr, hHo⟩)
      (.var (n + 1)) (.var n) := by
  intro ι u C r hu hC hr
  obtain ⟨c, rfl, hP, himg⟩ := hκ ι C r hC hr
  exact rnd_fresh hLr hHr hLo hHo htop hrow hu hP himg
end Fpy.DigitBound
