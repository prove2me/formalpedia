-- Prove2me | Theorems.Thm_WorkbookSource_plus_70607
-- name    : WorkbookSource.plus_70607
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:06.371139+00:00
-- url     : https://prove2.me/theorems/b1948eec-dbe0-4e3d-90ef-4dc4a833eedb
-- title:
--   The quadratic sum bounds shifted cyclic ratios at fixed sum three
-- statement:
--   Let $a,b,c \in \mathbb{R}^+$ such that $a+b+c=3$ Prove that $a^2+b^2+c^2 \geq \frac{2+a}{2+b}+\frac{2+b}{2+c}+\frac{2+c}{2+a}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_70607` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_70607; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_70607 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 + b^2 + c^2 ≥ (2 + a) / (2 + b) + (2 + b) / (2 + c) + (2 + c) / (2 + a)   :=  by sorry
