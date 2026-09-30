-- Prove2me | solution 1 for lean_workbook_plus_48545
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:09:45.76172+00:00
-- url     : https://prove2.me/submissions/a48977ce-f6fd-4a91-af81-67984c740b41

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : ℤ) (hab : a * b + b * c + c * a = 1) :
    ∃ k : ℤ, k ^ 2 = (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) := by
  refine ⟨a + b + c - a * b * c, ?_⟩
  have hid : (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) =
      (1 - (a * b + b * c + c * a)) ^ 2 + (a + b + c - a * b * c) ^ 2 := by
    ring
  simpa only [hab, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add] using hid.symm

#print axioms solution
