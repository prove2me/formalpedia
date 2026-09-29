-- Prove2me | Theorems.Thm_lean_workbook_plus_40279
-- name    : lean_workbook_plus_40279
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8dbb33ea-d655-4f5d-adc7-3d9dfeeb2fc8
-- statement:
--   Prove that for all real numbers $ a_{1} , a_{2} , ... , a_{n} $ where $a_i$ are distinct and $n>1$, the following equation holds: $ \frac{1}{(a_{1}-a_{2})(a_{1}-a_{3})...(a_{1}-a_{n})}+\frac{1}{(a_{2}-a_{1})(a_{2}-a_{3})...(a_{2}-a_{n})}+...+\frac{1}{(a_{n}-a_{1})(a_{n}-a_{2})...(a_{n}-a_{n-1})} = 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40279 (n : ℕ) (hn : 1 < n) (a : Fin n → ℝ) (ha : a.Injective) : ∑ i, (∏ j, (a i - a j))⁻¹ = 0   :=  by sorry
