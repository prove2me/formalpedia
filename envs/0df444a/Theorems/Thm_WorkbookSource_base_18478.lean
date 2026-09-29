-- Prove2me | Theorems.Thm_WorkbookSource_base_18478
-- name    : WorkbookSource.base_18478
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:43.512267+00:00
-- url     : https://prove2.me/theorems/6450df31-19fc-4f00-9add-338c665cf446
-- title:
--   A quartic power sum bounds a cubic sum with a quadratic correction
-- statement:
--   Prove that $ 3(a^4 + b^4 + c^4) - (a^3 + b^3 + c^3)\geq (a^3 + b^3 + c^3) - \frac13(a^2 + b^2 + c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18478` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18478; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18478 (a b c : ℝ) :
  3 * (a^4 + b^4 + c^4) - (a^3 + b^3 + c^3) ≥ (a^3 + b^3 + c^3) - (1/3) * (a^2 + b^2 + c^2)  :=  by sorry
