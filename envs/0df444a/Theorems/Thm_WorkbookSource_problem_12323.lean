-- Prove2me | Theorems.Thm_WorkbookSource_problem_12323
-- name    : WorkbookSource.problem_12323
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:44.680158+00:00
-- url     : https://prove2.me/theorems/d0186851-fa7a-459e-8608-fdc09ae4897d
-- title:
--   A rational midpoint lies strictly between its endpoints
-- statement:
--   If $\alpha, \beta$ are rational numbers then $\frac{\alpha+\beta}{2}$ is also rational. So, if we order the numbers, say $\alpha<\beta$ then: $$\alpha<\frac{\alpha+\beta}{2}<\beta$$ Doesn't this qualify?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12323` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12323; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_12323 : ∀ {α β : ℚ}, α < β → α < (α + β) / 2 ∧ (α + β) / 2 < β  :=  by sorry
