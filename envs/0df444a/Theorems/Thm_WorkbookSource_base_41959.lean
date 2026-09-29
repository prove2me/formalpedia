-- Prove2me | Theorems.Thm_WorkbookSource_base_41959
-- name    : WorkbookSource.base_41959
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:30.549855+00:00
-- url     : https://prove2.me/theorems/dde7735a-f0d0-490c-bbc3-6bef9dd9c7c0
-- title:
--   A symmetric sextic inequality with mixed coefficients
-- statement:
--   Prove $ 22\sum{a^6} - 36\sum{a^5(b+c)} + 657\sum{a^4(b^2+c^2)} - 420\sum{a^4bc} - 28\sum{a^3b^3} -540\sum{a^3bc(b+c)} + 792a^2b^2c^2 \ge 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41959` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41959; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41959 {a b c : ℝ} : 22 * (a^6 + b^6 + c^6) - 36 * (a^5 * (b + c) + b^5 * (a + c) + c^5 * (a + b)) + 657 * (a^4 * (b^2 + c^2) + b^4 * (a^2 + c^2) + c^4 * (a^2 + b^2)) - 420 * (a^4 * b * c + b^4 * a * c + c^4 * a * b) - 28 * (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) - 540 * (a^3 * b * c * (b + c) + b^3 * a * c * (a + c) + c^3 * a * b * (a + b)) + 792 * a^2 * b^2 * c^2 ≥ 0  :=  by sorry
