-- Prove2me | Theorems.Thm_lean_workbook_plus_82400
-- name    : lean_workbook_plus_82400
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e37b892b-80dc-497f-b3d8-3d5297165ff5
-- statement:
--   Let $n = 10100k + b$ , where $0 \le b < 10100$ . Then the given equation is equivalent to $1+10000k + \lfloor \frac{100b}{101} \rfloor = 9999k + \lceil \frac{99b}{100} \rceil$ . Thus $k = \lceil \frac{99b}{100} \rceil - \lfloor \frac{100b}{101} \rfloor - 1$ . For each b with $0 \le b < 10100$ , there must be exactly one k that satisfies this equation. Thus there are 10100 solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82400  (n b : ℕ)
  (h₀ : 0 ≤ b ∧ b < 10100)
  (h₁ : n = 10100 * k + b)
  (h₂ : 0 ≤ k ∧ k < 10100) :
  1 + 10000 * k + (100 * b / 101) = 9999 * k + (99 * b / 100)   :=  by sorry
