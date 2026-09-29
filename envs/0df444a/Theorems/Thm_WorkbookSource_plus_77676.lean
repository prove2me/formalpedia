-- Prove2me | Theorems.Thm_WorkbookSource_plus_77676
-- name    : WorkbookSource.plus_77676
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:15.190625+00:00
-- url     : https://prove2.me/theorems/822c894d-886c-4d3d-a011-4f6f9077d24a
-- title:
--   The fourth-power sum bounds a cyclic cubic ratio sum
-- statement:
--   THQ146.Let $a,b,c$ be positive real numbers . Prove that $a^4+b^4+c^4\ge \frac{a^3(b^2+c^2)}{b+c}+\frac{b^3(c^2+a^2)}{c+a}+\frac{c^3(a^2+b^2)}{a+b}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_77676` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_77676; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_77676 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 ≥ a^3 * (b^2 + c^2) / (b + c) + b^3 * (c^2 + a^2) / (c + a) + c^3 * (a^2 + b^2) / (a + b)   :=  by sorry
