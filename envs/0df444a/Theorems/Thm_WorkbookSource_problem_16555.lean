-- Prove2me | Theorems.Thm_WorkbookSource_problem_16555
-- name    : WorkbookSource.problem_16555
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:06.570499+00:00
-- url     : https://prove2.me/theorems/2171f6ce-665b-4096-beb6-62b995eba685
-- title:
--   A homogeneous fourth-degree inequality
-- statement:
--   $PA^4+PB^4+PC^4\ge \frac 13\cdot a^4 \iff 6\sum_{cyc}x^4+9\sum_{cyc}x^2y^2+6\sum_{sym}x^3y \ge (x+y+z)^4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16555` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16555; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16555 : ∀ x y z : ℝ, 6 * (x^4 + y^4 + z^4) + 9 * (x^2 * y^2 + x^2 * z^2 + y^2 * z^2) + 6 * (x^3 * y + x^3 * z + y^3 * x + y^3 * z + z^3 * x + z^3 * y) ≥ (x + y + z)^4  :=  by sorry
