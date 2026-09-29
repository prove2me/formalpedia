-- Prove2me | Theorems.Thm_WorkbookSource_problem_3247
-- name    : WorkbookSource.problem_3247
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:39.566511+00:00
-- url     : https://prove2.me/theorems/09900782-da3e-483b-8d7d-2cac967a9e90
-- title:
--   A quartic inequality in two variables
-- statement:
--   Expanding and simplifying we get:
--
--    $(yz-2y-2z)^2\geq 2yz(2-y-z)\iff y^2z^2 +4y^2+4z^2 \geq 4yz +2y^z+2yz^2$
--
--    Now by AM-GM:
--
--    ${\frac{y^2z^2}{2}+2y^2} \geq 2\sqrt{y^4z^2}=2y^2z$
--
--    Similarly $\frac{y^2z^2}{2} +2z^2 \geq 2yz^2$
--   Also, $2y^2+2z^2\geq 4yz$ by sums of squares
--   Summing the three inequalities yields the result
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3247` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3247; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3247  (y z : ℝ) :
  (y * z - 2 * y - 2 * z)^2 ≥ 2 * y * z * (2 - y - z)  :=  by sorry
