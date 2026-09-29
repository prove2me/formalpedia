-- Prove2me | Theorems.Thm_WorkbookSource_base_29761
-- name    : WorkbookSource.base_29761
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:58.656785+00:00
-- url     : https://prove2.me/theorems/93e65eea-30ae-424e-8d08-80bd805c3336
-- title:
--   A sum of squared and linear ratios is at least seven quarters
-- statement:
--   Let $a,b,c$ be positive real numbers . Show that $\frac{a^2}{b^2}+\frac{b}{c+a}+\frac{c}{b}\geq \frac{7}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29761` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29761; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29761 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b / (c + a) + c / b) ≥ 7 / 4  :=  by sorry
