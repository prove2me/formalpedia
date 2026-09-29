-- Prove2me | Theorems.Thm_WorkbookSource_problem_24413
-- name    : WorkbookSource.problem_24413
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:51:58.7274+00:00
-- url     : https://prove2.me/theorems/c6f29926-a677-4f9d-951a-3972107ac88c
-- title:
--   A strict square-root bound
-- statement:
--   basically we want x>point of equality, since after the point of equality, the difference between 2x and sqrtx grow exponentially (2x is always bigger after point of equality). the 2 points of equality of $ \sqrt{x}=2x$ are $ \frac{1}{4}$ and 0. so we take x>the larger of the 2, or $ x>\frac{1}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24413` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24413; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24413 : ∀ x > 1/4, Real.sqrt x < 2 * x  :=  by sorry
