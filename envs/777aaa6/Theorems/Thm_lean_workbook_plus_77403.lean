-- Prove2me | Theorems.Thm_lean_workbook_plus_77403
-- name    : lean_workbook_plus_77403
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/be13ea4c-fc61-45ce-baef-2d4fc84f3317
-- statement:
--   If $5 \mid a$ and $2 \mid a$ , then $a^4 \equiv 0 \pmod{10}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77403 : 5 ∣ a ∧ 2 ∣ a → a^4 ≡ 0 [ZMOD 10]   :=  by sorry
