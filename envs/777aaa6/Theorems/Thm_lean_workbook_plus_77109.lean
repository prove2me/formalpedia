-- Prove2me | Theorems.Thm_lean_workbook_plus_77109
-- name    : lean_workbook_plus_77109
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0b7aaf16-07a3-48d5-b1a9-3f552103d828
-- statement:
--   $\sum_{cyc} \frac{a - bc}{a + bc} \leq \frac{3}{2}$\n\n$\Longleftrightarrow \sum{\frac{bc}{a+bc}}\ge \frac{3}{4}$\n\n$\Longleftrightarrow \sum{\frac{bc}{(a+b)(a+c)}}\ge \frac{3}{4}$\n\n$\Longleftrightarrow 4 \sum{bc(b+c)} \ge 3(a+b)(b+c)(c+a)$\n\n$\Longleftrightarrow (a+b)(b+c)(c+a) \ge 8abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77109 :
  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c   :=  by sorry
