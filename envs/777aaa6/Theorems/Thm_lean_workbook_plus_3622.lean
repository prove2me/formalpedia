-- Prove2me | Theorems.Thm_lean_workbook_plus_3622
-- name    : lean_workbook_plus_3622
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b40803d9-c5c0-45c8-8ea9-e9006ff6daa3
-- statement:
--   Each factor $k$ is of the form $2^a \cdot 3^b \cdot 5^c$ where $a$ , $b$ , $c$ are positive integers and $0 \le a \le 5$ , $0 \le b \le 4$ and $0 \le c \le 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3622 ∀ k : ℕ, (∃ a b c : ℕ, (0 ≤ a ∧ a ≤ 5 ∧ 0 ≤ b ∧ b ≤ 4 ∧ 0 ≤ c ∧ c ≤ 2 ∧ k = 2^a * 3^b * 5^c))   :=  by sorry
