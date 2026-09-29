-- Prove2me | Theorems.Thm_lean_workbook_plus_18581
-- name    : lean_workbook_plus_18581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/50737ef7-c34b-47ad-b1b9-1d7f7651da0e
-- statement:
--   The given inequality is equivalent to $a^3-c^3 \geq 3b(a-c)(a+c-b) \iff a^2+ac+c^2 \geq 3b(a+c-b)$ , which with the hypotheses $b=c+r, a=c+r+s$ ( $r, s \in \mathbb{R}^+$ ) becomes $(r-s)^2 \geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18581  (b c a r s : ℝ)
  (h₀ : 0 < r ∧ 0 < s)
  (h₁ : b = c + r)
  (h₂ : a = c + r + s) :
  (a^3 - c^3 - 3 * b * (a - c) * (a + c - b) ≥ 0) ↔ (a^2 + a * c + c^2 - 3 * b * (a + c - b) ≥ 0)   :=  by sorry
