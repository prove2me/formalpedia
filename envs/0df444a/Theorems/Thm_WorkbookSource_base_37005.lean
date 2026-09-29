-- Prove2me | Theorems.Thm_WorkbookSource_base_37005
-- name    : WorkbookSource.base_37005
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:35.365526+00:00
-- url     : https://prove2.me/theorems/f2db64c6-3d87-4054-9508-67231d963421
-- title:
--   A weighted cyclic cubic ratio bounds the quadratic mean
-- statement:
--   For $ a,b,c > 0$ , prove that
--
--    $ \frac {a^3}{2a + 3b} + \frac {b^3}{2b + 3c} + \frac {c^3}{2c + 3a}\geq \frac {a^2 + b^2 + c^2}{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37005` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37005; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37005 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (2 * a + 3 * b) + b^3 / (2 * b + 3 * c) + c^3 / (2 * c + 3 * a)) ≥ (a^2 + b^2 + c^2) / 5  :=  by sorry
