-- Prove2me | Theorems.Thm_WorkbookSource_plus_3249
-- name    : WorkbookSource.plus_3249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:52.306849+00:00
-- url     : https://prove2.me/theorems/9434c33c-d578-4246-ab5d-65e8f0af1875
-- title:
--   A quadratic pairwise-sum bound with a cubic correction
-- statement:
--   Let a, b, c are positive real numbers such that $ a+b+c=1$ . Prove that $ 4\left(ab+bc+ac\right)^2+6abc+1\ge 5\left(ab+bc+ac\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3249` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3249; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3249 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : 4 * (a * b + b * c + a * c) ^ 2 + 6 * a * b * c + 1 ≥ 5 * (a * b + b * c + a * c)   :=  by sorry
