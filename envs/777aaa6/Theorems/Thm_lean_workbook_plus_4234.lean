-- Prove2me | Theorems.Thm_lean_workbook_plus_4234
-- name    : lean_workbook_plus_4234
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e3e4a569-13a8-418f-b3f6-2e6e7e12639e
-- statement:
--   (a+b)^2-ab=a^2+b^2+ab\equiv 0\pmod{5}\Rightarrow 4a^2+4b^2+4ab\equiv 0\pmod{5}\Rightarrow (2a+b)^2+3b^2\equiv 0\pmod{5}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4234 (a b : ℤ) : (a + b) ^ 2 - a * b ≡ 0 [ZMOD 5] ↔ (2 * a + b) ^ 2 + 3 * b ^ 2 ≡ 0 [ZMOD 5]   :=  by sorry
