-- Prove2me | Theorems.Thm_lean_workbook_plus_12567
-- name    : lean_workbook_plus_12567
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/22511f4c-9636-4661-828d-2a7fe84e4d28
-- statement:
--   Prove $ \frac {1}{n + 1}(\frac {1}{1} + \frac {1}{3} + ... + \frac {1}{2n - 1}) \ge \frac {1}{n}(\frac {1}{2} + \frac {1}{4} + ... + \frac {1}{2n})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12567 : ∀ n : ℕ, (1 / (n + 1)) * ∑ i in Finset.range n, (1 / (2 * i + 1)) ≥ (1 / n) * ∑ i in Finset.range n, (1 / (2 * i + 2))   :=  by sorry
