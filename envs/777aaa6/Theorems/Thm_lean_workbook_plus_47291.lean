-- Prove2me | Theorems.Thm_lean_workbook_plus_47291
-- name    : lean_workbook_plus_47291
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/2ec9fd3c-80ce-4917-b5fe-1e82dfc35a91
-- statement:
--   Show that $S_{n}=\frac{1}{2} \cdot \frac{3}{4} ... \cdot \frac{2n-1}{2n} \le T_{n}= \frac{2}{3} \cdot \frac{4}{5} ... \cdot \frac{2n}{2n+1}$ and deduce that $S_{n}$ approaches $0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47291 : ∀ n : ℕ, (∏ i in Finset.range n, (2 * i - 1) / (2 * i)) ≤ (∏ i in Finset.range n, (2 * i) / (2 * i + 1))   :=  by sorry
