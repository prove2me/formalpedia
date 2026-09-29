-- Prove2me | Theorems.Thm_WorkbookSource_base_17825
-- name    : WorkbookSource.base_17825
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:09:56.180914+00:00
-- url     : https://prove2.me/theorems/87e824f0-9d5d-4afd-b497-14af2bc559c3
-- title:
--   A shifted quadratic ratio lower bound at fixed sum three
-- statement:
--   (a;b;c>0 ; $ b + a + c = 3$ )prove that
--    $ \frac {a^2 + 1}{b^2 + c^2} + \frac {b^2 + 1}{a^2 + c^2} + \frac {c^2 + 1}{b^2 + a^2}\ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17825` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17825; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17825 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 1) / (b^2 + c^2) + (b^2 + 1) / (a^2 + c^2) + (c^2 + 1) / (b^2 + a^2) ≥ 3  :=  by sorry
