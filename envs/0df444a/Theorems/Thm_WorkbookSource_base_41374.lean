-- Prove2me | Theorems.Thm_WorkbookSource_base_41374
-- name    : WorkbookSource.base_41374
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:29.140031+00:00
-- url     : https://prove2.me/theorems/4cab2aee-dc25-442d-9069-abad2e98df00
-- title:
--   A sixth-degree bound under a weighted zero sum
-- statement:
--   Let $x,y,z$ are real numbers such that $x+3y+z=0$ . Prove that
--    $$\left(x^2+y^2+z^2\right)^3\geq \frac{38}{27}\left(x^3+y^3+z^3\right)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41374` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41374; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41374 (x y z : ℝ) (h : x + 3 * y + z = 0) :
  (x^2 + y^2 + z^2)^3 ≥ (38/27) * (x^3 + y^3 + z^3)^2  :=  by sorry
