-- Prove2me | Theorems.Thm_lean_workbook_plus_71448
-- name    : lean_workbook_plus_71448
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3784e0ee-ac70-4973-8380-eecec04f02d7
-- statement:
--   If $b$ is a multiple of $5$, then $a \equiv 0 \pmod{5}$ implies $a+b^{2014} \equiv 0 \pmod{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71448 : 5 ∣ b → a ≡ 0 [ZMOD 5] → a + b^2014 ≡ 0 [ZMOD 5]   :=  by sorry
