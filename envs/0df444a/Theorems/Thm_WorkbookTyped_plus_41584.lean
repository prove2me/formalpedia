-- Prove2me | Theorems.Thm_WorkbookTyped_plus_41584
-- name    : WorkbookTyped.plus_41584
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:48.947995+00:00
-- url     : https://prove2.me/theorems/a9763e99-4a23-460e-9a4d-5b45ab909da4
-- title:
--   Equivalent divisibility conditions over the integers
-- statement:
--   Let $a$ and $b$ be integers. Show that $29$ divides $3a+2b$ if and only if it divides $11a+17b$ .
--
--   Declaration repair: Added explicit integer binders (a b : ℤ), as required by the source wording. The malformed platform declaration has undeclared variables; its inferred natural-number interpretation is not retained.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_41584` (Apache-2.0). [Original malformed declaration](https://prove2.me/theorems/3a22f5a1-05c4-467a-9080-8d65091b0c25). This record proves the corrected statement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_41584; explicit variable-declaration repair; Apache-2.0

import Mathlib

theorem WorkbookTyped.plus_41584 (a b : ℤ) : 29 ∣ (3 * a + 2 * b) ↔ 29 ∣ (11 * a + 17 * b)   :=  by sorry
