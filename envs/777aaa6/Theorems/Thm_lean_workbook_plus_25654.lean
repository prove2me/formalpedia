-- Prove2me | Theorems.Thm_lean_workbook_plus_25654
-- name    : lean_workbook_plus_25654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4dc08c84-dbca-4c30-9d98-c9041bdb7448
-- statement:
--   $ Assum a \le\ 0;b,c \ge\ 0$ so $ |a| \ge\ b + c \rightarrow q \le\ 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25654 (a b c q : ℝ) (h₁ : a ≤ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ q = (b + c - |a|) * (b + c + |a|)) : |a| ≥ b + c → q ≤ 0   :=  by sorry
