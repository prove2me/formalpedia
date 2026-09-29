-- Prove2me | Theorems.Thm_lean_workbook_plus_66087
-- name    : lean_workbook_plus_66087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/df6247c1-b295-41d1-a1a0-40704a176a97
-- statement:
--   Using Fermat's Little Theorem (FLT), show that for $a\not\equiv 0\pmod{3}$, $a^2\equiv 1\pmod{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66087 (a : ℤ) (ha : ¬ a ≡ 0 [ZMOD 3]) : a ^ 2 ≡ 1 [ZMOD 3]   :=  by sorry
