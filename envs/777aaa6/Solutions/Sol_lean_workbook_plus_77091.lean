-- Prove2me | solution 1 for lean_workbook_plus_77091
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:48.215282+00:00
-- url     : https://prove2.me/submissions/78fed0f1-855c-42a0-8e89-b15c2827d073

import Mathlib

set_option autoImplicit false

theorem solution (a b c d k : ℤ) (h₁ : a ≡ c [ZMOD k])
    (h₂ : b ≡ d [ZMOD k]) : a + b ≡ c + d [ZMOD k] := by
  exact h₁.add h₂
