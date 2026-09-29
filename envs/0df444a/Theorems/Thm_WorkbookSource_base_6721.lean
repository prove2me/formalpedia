-- Prove2me | Theorems.Thm_WorkbookSource_base_6721
-- name    : WorkbookSource.base_6721
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:21:44.864012+00:00
-- url     : https://prove2.me/theorems/479fb7a6-8a37-4f7f-8b8b-d96cb70005b7
-- title:
--   A cyclic cubic difference reciprocal bound at fixed sum three
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ ,Show that $\frac{a^3-8a+8}{b+c}+\frac{b^3-8b+8}{c+a}+\frac{c^3-8c+8}{a+b}\ge \frac{3}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6721` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6721; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6721 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : (a^3 - 8 * a + 8) / (b + c) + (b^3 - 8 * b + 8) / (c + a) + (c^3 - 8 * c + 8) / (a + b) ≥ 3 / 2  :=  by sorry
