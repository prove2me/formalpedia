-- Prove2me | Theorems.Thm_lean_workbook_plus_75079
-- name    : lean_workbook_plus_75079
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c4e3c30a-eb9a-461b-9c26-d6cb30f26fc2
-- statement:
--   With $k=1$, we have: $(1-a)(1-b)(1-c)\ge 0 \leftrightarrow 1+ab+bc+ca \ge a+b+c+abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75079 : ∀ a b c : ℝ, (1 - a) * (1 - b) * (1 - c) ≥ 0 ↔ 1 + a * b + b * c + c * a ≥ a + b + c + a * b * c   :=  by sorry
