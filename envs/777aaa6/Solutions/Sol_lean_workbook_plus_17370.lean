-- Prove2me | solution 1 for lean_workbook_plus_17370
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:24.241291+00:00
-- url     : https://prove2.me/submissions/0a5e7636-68ac-4f7b-9c85-5c2cac5d6b63

import Mathlib.Analysis.Complex.Basic

theorem solution {a₁ a₂ b₁ b₂ m : ℤ} (ha : a₁ ≡ a₂ [ZMOD m]) (hb : b₁ ≡ b₂ [ZMOD m]) : a₁ + b₁ ≡ a₂ + b₂ [ZMOD m] :=
  Int.ModEq.add ha hb
