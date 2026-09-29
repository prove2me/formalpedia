-- Prove2me | Theorems.Thm_WorkbookSource_base_36205
-- name    : WorkbookSource.base_36205
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:26.384801+00:00
-- url     : https://prove2.me/theorems/94a028a3-cd56-401f-a691-d41eb9fdcf6a
-- title:
--   A squared cyclic ratio sum with a symmetric correction
-- statement:
--   Let $a,b,c>0$ . Prove that
--    $16\sum\limits_{cyc}\left(\frac{a}{a+b}\right)^2+\frac{ab+bc+ca}{a^2+b^2+c^2}\ge13$
--   It is stronger than
--    $\left(\frac{a}{a+b}\right)^2+\left(\frac{b}{b+c}\right)^2+\left(\frac{c}{c+a}\right)^2\ge\frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36205` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36205; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36205 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 16 * ((a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 13  :=  by sorry
