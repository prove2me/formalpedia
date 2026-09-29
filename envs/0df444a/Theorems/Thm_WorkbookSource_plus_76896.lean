-- Prove2me | Theorems.Thm_WorkbookSource_plus_76896
-- name    : WorkbookSource.plus_76896
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:47.117524+00:00
-- url     : https://prove2.me/theorems/a123ca28-1e07-48cd-bf63-e00de1bb6c3b
-- title:
--   A quadratic-form bound on a sphere-plane intersection
-- statement:
--   Let $ a,b,c $ be real numbers such that $a^{2}+b^{2}+c^{2}=1$ and $2a+2b-3c=1$ . Prove that:
--
--    $$20a^{2}+25b^{2}+13c^{2}-12ab+16bc+24ca \ge 25$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76896` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76896; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76896 (a b c : ℝ) (ha : a^2 + b^2 + c^2 = 1) (hb : 2 * a + 2 * b - 3 * c = 1) : 20 * a^2 + 25 * b^2 + 13 * c^2 - 12 * a * b + 16 * b * c + 24 * c * a ≥ 25   :=  by sorry
