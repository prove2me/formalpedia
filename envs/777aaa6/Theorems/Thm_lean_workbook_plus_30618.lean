-- Prove2me | Theorems.Thm_lean_workbook_plus_30618
-- name    : lean_workbook_plus_30618
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/96e6598b-ca5f-415f-a5b3-3822af692532
-- statement:
--   Show that, $\frac{1}{\sqrt{4n}}\leq(\frac{1}{2})(\frac{3}{4})\cdots(\frac{2n-1}{2n})$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30618 : ∀ n : ℕ, (1 / (Real.sqrt (4 * n))) ≤ (∏ i in Finset.range n, ((2 * i - 1) / (2 * i)))   :=  by sorry
