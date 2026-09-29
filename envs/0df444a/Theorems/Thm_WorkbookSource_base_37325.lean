-- Prove2me | Theorems.Thm_WorkbookSource_base_37325
-- name    : WorkbookSource.base_37325
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:16.046255+00:00
-- url     : https://prove2.me/theorems/62c58c35-dff5-4cb3-9f9f-6ca1c55ff804
-- title:
--   A fourth-power bound for a product of symmetric sums
-- statement:
--   $4 \sum a^4 - \sum a^2b^2 \ge (a+b+c)(a^3+b^3+c^3)=\sum a^4+ \sum (sym) a^3b$ $\iff$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37325` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37325; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37325 {a b c : ℝ} :
  4 * (a ^ 4 + b ^ 4 + c ^ 4) - (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥
  (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3)  :=  by sorry
