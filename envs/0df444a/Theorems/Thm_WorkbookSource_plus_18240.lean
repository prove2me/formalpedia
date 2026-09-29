-- Prove2me | Theorems.Thm_WorkbookSource_plus_18240
-- name    : WorkbookSource.plus_18240
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:29:59.53521+00:00
-- url     : https://prove2.me/theorems/72fcbd53-f475-4970-ae5a-1a5e6e1cbff9
-- title:
--   A power of six factorial divides its iterated factorial
-- statement:
--   Show that $(6!)^{5!}$ is a divisor of $(6!)!$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_18240` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_18240; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_18240 : (6!)^5! ∣ (6!)!   :=  by sorry
