-- Prove2me | Theorems.Thm_lean_workbook_plus_75706
-- name    : lean_workbook_plus_75706
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bc8db50c-db1d-4883-8b3e-29c1f49e5bd9
-- statement:
--   Consider $ a\geq b \geq c \Longrightarrow A = a^ab^cc^b + b^bc^aa^c + c^cb^aa^b \leq B = 3a^ab^bc^c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75706 (a b c : ℝ) (ha : a ≥ b ∧ b ≥ c) : a^a * b^b * c^c + b^b * c^c * a^a + c^c * a^a * b^b ≤ 3 * a^a * b^b * c^c   :=  by sorry
