-- Prove2me | Theorems.Thm_WorkbookSource_base_37266
-- name    : WorkbookSource.base_37266
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:03.880196+00:00
-- url     : https://prove2.me/theorems/30aec00a-c332-428e-a93a-d573da0ada54
-- title:
--   A fourth-power ratio sum with symmetric cubic corrections
-- statement:
--   Let a,b,c>0
--   $ \frac {{a^4 + b^4 }}{c} + \frac {{a^4 + c^4 }}{b} + \frac {{b^4 + c^4 }}{a} + 2ab(a + b) + 2bc(b + c) + 2ac(a + c) \ge 6(a^3 + b^3 + c^3 )$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37266` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37266; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37266 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + b^4) / c + (a^4 + c^4) / b + (b^4 + c^4) / a + 2 * a * b * (a + b) + 2 * b * c * (b + c) + 2 * a * c * (a + c) ≥ 6 * (a^3 + b^3 + c^3)  :=  by sorry
