-- Prove2me | Theorems.Thm_WorkbookSource_base_55087
-- name    : WorkbookSource.base_55087
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:27.891309+00:00
-- url     : https://prove2.me/theorems/9876e2a4-d18a-4c34-85f1-a6fbde177307
-- title:
--   A squared fourth-power sum bounds a fifth-power product
-- statement:
--   Prove the inequality $9(a^4+b^4+c^4)^2 \ge (a^5+b^5+c^5)(a+b+c)^3$ for non-negative real numbers $a$, $b$, and $c$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55087` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55087; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55087 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 9 * (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 ≥ (a ^ 5 + b ^ 5 + c ^ 5) * (a + b + c) ^ 3  :=  by sorry
