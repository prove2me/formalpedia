-- Prove2me | Theorems.Thm_lean_workbook_plus_82554
-- name    : lean_workbook_plus_82554
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e280eb89-d4fc-4d50-b64e-da30c10dc7bc
-- statement:
--   Prove that $ \frac {3}{2} \ge \frac {1}{2!}1 + \frac {1}{3!}(1 + 2) + ... + \frac {1}{n!}(1 + ... + n)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82554 : ∀ n, (3 : ℝ) / 2 ≥ ∑ k in Finset.range n, (1 : ℝ) / (k + 1)! * (∑ l in Finset.range k, l + 1)   :=  by sorry
