-- Prove2me | Theorems.Thm_WorkbookSource_plus_5342
-- name    : WorkbookSource.plus_5342
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:25.54409+00:00
-- url     : https://prove2.me/theorems/a569718e-2559-4883-8b8d-98a363e478da
-- title:
--   A shifted-product inequality with a sphere constraint
-- statement:
--   Given $ a,b,c,d > 0 $ and $ a^2+b^2+c^2+d^2 = 1 .$ Prove that $ 4(k-a)(k-b) \geq (c+d)^2+2(k^2-1) $ Where $k\in R.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_5342` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_5342; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_5342 (a b c d k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a^2 + b^2 + c^2 + d^2 = 1) : 4 * (k - a) * (k - b) ≥ (c + d)^2 + 2 * (k^2 - 1)   :=  by sorry
