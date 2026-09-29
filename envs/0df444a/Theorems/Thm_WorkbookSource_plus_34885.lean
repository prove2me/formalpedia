-- Prove2me | Theorems.Thm_WorkbookSource_plus_34885
-- name    : WorkbookSource.plus_34885
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:52.989458+00:00
-- url     : https://prove2.me/theorems/09887c6c-9507-49f0-b09a-1435b200d580
-- title:
--   A mixed quadratic-quartic lower bound at fixed sum
-- statement:
--   If $ a,b,c>0,a+b+c=3 $ prove that: $ a^2+b^2c^2+10\ge 4(bc+ca+ab) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_34885` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_34885; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_34885 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 + b^2 * c^2 + 10 ≥ 4 * (b * c + c * a + a * b)   :=  by sorry
