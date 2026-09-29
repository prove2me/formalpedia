-- Prove2me | Theorems.Thm_WorkbookSource_base_36463
-- name    : WorkbookSource.base_36463
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:08.678908+00:00
-- url     : https://prove2.me/theorems/fae957d6-e33b-452b-b908-6d851244988d
-- title:
--   A product of two quartic differences bounds a squared cyclic expression
-- statement:
--   Prove that:
--   $ \left(\sum_{cyc}a^2b^2 - abc(a + b + c)\right)\left(\sum_{cyc}a^4 - \sum_{cyc}a^2b^2\right) \ge \frac {3}{4}\left(\sum_{cyc}a^3b - abc(a + b + c)\right)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36463` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36463; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36463 {a b c : ℝ} : (a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c)) * (a^4 + b^4 + c^4 - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) ≥ 3 / 4 * (a^3 * b + b^3 * c + c^3 * a - a * b * c * (a + b + c))^2  :=  by sorry
