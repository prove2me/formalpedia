-- Prove2me | solution 1 for Fpy.DigitBound.Term.Below.rename_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:46:24.549485+00:00
-- url     : https://prove2.me/submissions/67ebfb17-252a-4fec-8fff-70ed3cc55ac8

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg


set_option autoImplicit true
open Fpy Fpy.DigitBound
namespace Fpy.DigitBound
namespace Term.Below
theorem _root_.solution {a b n : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    ∀ {t : Term}, t.Below b → (t.rename (shift a b n)).Below (n + (b - a)) := fun {t} ht => match t, ht with
  | .const _, _ => trivial
  | .var x, hx => by
    have hx : x < b := hx
    change shift a b n x < _
    unfold shift
    split_ifs <;> omega
  | .add _ _, ⟨hs, ht⟩ | .max _ _, ⟨hs, ht⟩ | .min _ _, ⟨hs, ht⟩ =>
    ⟨solution hab hbn hs, solution hab hbn ht⟩
  | .neg t, ht => solution (t := t) hab hbn ht
  | .smul _ t, ht => solution (t := t) hab hbn ht
end Term.Below
end Fpy.DigitBound
