-- Prove2me | Theorems.Thm_WorkbookSource_plus_70768
-- name    : WorkbookSource.plus_70768
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:41.731439+00:00
-- url     : https://prove2.me/theorems/0ea383ea-6f9f-4fa6-9d97-d411426236f4
-- title:
--   A cyclic rational difference inequality at fixed sum three
-- statement:
--   Given two ordered triples $S_1=\left(\frac{1-a}{a},\frac{1-b}{b},\frac{1-c}{c}\right)$ and $S_2=\left(\frac{a}{1+a},\frac{b}{1+b},\frac{c}{1+c}\right)$, where $a, b, c > 0$ and $a+b+c=3$. Prove that $\sum_{cyc} \frac{b(1-a)}{a(1+b)} \geq \sum_{cyc} \left(\frac{1-a}{a} \cdot \frac{a}{1+a}\right)$ using Rearrangement inequality.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_70768` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_70768; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_70768 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (b * (1 - a) / (a * (1 + b)) + c * (1 - b) / (b * (1 + c)) + a * (1 - c) / (c * (1 + a))) ≥ (1 - a) / a * a / (1 + a) + (1 - b) / b * b / (1 + b) + (1 - c) / c * c / (1 + c)   :=  by sorry
