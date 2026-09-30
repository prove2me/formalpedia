-- Prove2me | solution 1 for lean_workbook_plus_50552
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:09:55.289149+00:00
-- url     : https://prove2.me/submissions/532b7b37-8de8-45d4-8a6e-a0e02d55d5aa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution {a b c : ℤ} :
    5 * (a - b) * (b - c) * (c - a) ∣
      (a - b) ^ 5 + (b - c) ^ 5 + (c - a) ^ 5 := by
  refine ⟨a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a, ?_⟩
  ring

#print axioms solution
