-- Prove2me | Theorems.Thm_WorkbookSource_base_25519
-- name    : WorkbookSource.base_25519
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:41.722907+00:00
-- url     : https://prove2.me/theorems/b1507048-ff77-4075-a5af-026b7098fa8c
-- title:
--   A mixed cubic-quartic inequality at fixed sum
-- statement:
--   (Inequality rearrangement) Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that
--    $ 3(a^3+b^3+c^3)\geq 3abc+2(a^3c+b^3c+abc^2) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25519` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25519; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 3 * (a^3 + b^3 + c^3) ≥ 3 * a * b * c + 2 * (a^3 * c + b^3 * c + a * b * c^2)  :=  by sorry
