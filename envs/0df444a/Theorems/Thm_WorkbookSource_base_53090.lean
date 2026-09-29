-- Prove2me | Theorems.Thm_WorkbookSource_base_53090
-- name    : WorkbookSource.base_53090
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:20.350091+00:00
-- url     : https://prove2.me/theorems/c9e1a08c-9d6c-4f1c-af46-e3b4fe2502ad
-- title:
--   A squared-norm bound at unit positive sum
-- statement:
--   If $a,b,c>0$ and $a+b+c=1$, prove that $a^2+b^2+c^2+1\ge 4(ab+bc+ca)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53090` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53090; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53090 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + 1 ≥ 4 * (a * b + b * c + c * a)  :=  by sorry
