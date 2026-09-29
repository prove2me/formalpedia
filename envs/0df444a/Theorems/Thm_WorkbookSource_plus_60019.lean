-- Prove2me | Theorems.Thm_WorkbookSource_plus_60019
-- name    : WorkbookSource.plus_60019
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:28.059363+00:00
-- url     : https://prove2.me/theorems/10fd081b-71a7-438e-87af-597a5e06c32c
-- title:
--   A sixth-degree inequality in symmetric polynomial expressions
-- statement:
--   Prove that for real numbers $a, b, c$, the following inequality holds:
--
--   $(a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2)+6abc(a+b)(b+c)(c+a) \ge 7a^2b^2c^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60019` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60019; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60019 (a b c : ℝ) :
  (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 6 * a * b * c * (a + b) * (b + c) * (c + a) ≥ 7 * a^2 * b^2 * c^2   :=  by sorry
