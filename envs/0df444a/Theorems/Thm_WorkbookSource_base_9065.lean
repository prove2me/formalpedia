-- Prove2me | Theorems.Thm_WorkbookSource_base_9065
-- name    : WorkbookSource.base_9065
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:22:40.534204+00:00
-- url     : https://prove2.me/theorems/f59b54fe-4f83-4535-a7c2-78c51b8eb7b9
-- title:
--   Comparing powers of two with exponential exponents
-- statement:
--   Prove that $2^{3^{100}}>2^{2^{151}}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9065` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9065; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9065 : 2^(3^100) > 2^(2^151)  :=  by sorry
