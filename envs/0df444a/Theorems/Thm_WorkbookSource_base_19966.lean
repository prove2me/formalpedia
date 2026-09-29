-- Prove2me | Theorems.Thm_WorkbookSource_base_19966
-- name    : WorkbookSource.base_19966
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:09:47.571002+00:00
-- url     : https://prove2.me/theorems/88ac915e-9698-41c7-8607-ea6af68109bb
-- title:
--   Two shifted square-root squared reciprocals have a sum lower bound
-- statement:
--   Prove that for $ x,y\in\mathbb{R^ + }$ , $ \frac {1}{(1 + \sqrt {x})^{2}} + \frac {1}{(1 + \sqrt {y})^{2}} \ge \frac {2}{x + y + 2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19966` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19966; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19966 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2) ≥ 2 / (x + y + 2)  :=  by sorry
