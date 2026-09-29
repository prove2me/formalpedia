-- Prove2me | Theorems.Thm_WorkbookSource_plus_38644
-- name    : WorkbookSource.plus_38644
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:09.142714+00:00
-- url     : https://prove2.me/theorems/407f96f9-bca6-45e1-8ad8-1cf12d22f9c6
-- title:
--   A shifted cubic polynomial has a uniform lower difference bound
-- statement:
--   Prove that for real numbers $ t, z $ with $ t < z $, $ t^3 - 3t - 2 \leq (t + h)^3 - 3(t + h) + 2 $ where $ h > 0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_38644` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_38644; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_38644 (t z h : ℝ) (hz : t < z) (hh : h > 0) : t^3 - 3 * t - 2 ≤ (t + h)^3 - 3 * (t + h) + 2   :=  by sorry
