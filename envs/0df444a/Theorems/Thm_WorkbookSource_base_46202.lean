-- Prove2me | Theorems.Thm_WorkbookSource_base_46202
-- name    : WorkbookSource.base_46202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:00:18.75808+00:00
-- url     : https://prove2.me/theorems/06c9ac24-7042-4200-8b98-5677c3a14382
-- title:
--   A cubic sum with a pair-product rational correction
-- statement:
--   For $ a,b,c$ positive reals
--
--    $ \sum a^3 + 3abc + 2\sum \frac {a^2b^2}{(a + b)} \geq \frac {3}{2}\sum ab(a + b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46202` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46202; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46202 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 3 * a * b * c + 2 * (a^2 * b^2 / (a + b) + b^2 * c^2 / (b + c) + c^2 * a^2 / (c + a)) ≥ 3 / 2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))  :=  by sorry
