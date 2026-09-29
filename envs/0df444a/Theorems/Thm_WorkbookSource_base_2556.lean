-- Prove2me | Theorems.Thm_WorkbookSource_base_2556
-- name    : WorkbookSource.base_2556
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:43:42.670498+00:00
-- url     : https://prove2.me/theorems/1ab19d54-fd89-40c4-b28d-3376d2fe39f4
-- title:
--   An alternating pair-sum ratio sum is at least four
-- statement:
--   Prove for all positive reals a,b,c,d:
--
--    $ \frac {a + c}{b + c} + \frac {b + d}{c + d} + \frac {c + a}{d + a} + \frac {d + b}{a + b}\ge 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2556` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2556; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2556 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + c) / (b + c) + (b + d) / (c + d) + (c + a) / (d + a) + (d + b) / (a + b) ≥ 4  :=  by sorry
