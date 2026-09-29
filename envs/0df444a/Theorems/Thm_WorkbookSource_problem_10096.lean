-- Prove2me | Theorems.Thm_WorkbookSource_problem_10096
-- name    : WorkbookSource.problem_10096
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:38.443838+00:00
-- url     : https://prove2.me/theorems/bbc4d6f1-717e-447d-a58f-dcc1f4da96dd
-- title:
--   A cubic inequality for three nonnegative variables
-- statement:
--   If $x, y, z \ge 0$, prove: $\frac{3}{2} (x+y+z)[3(x+y+z)^2+xy+yz+zx] \ge (3x+y+z)(3y+x+z)(3z+x+y)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10096` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10096; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_10096 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (3 / 2) * (x + y + z) * (3 * (x + y + z) ^ 2 + x * y + x * z + y * z) ≥ (3 * x + y + z) * (3 * y + x + z) * (3 * z + x + y)  :=  by sorry
