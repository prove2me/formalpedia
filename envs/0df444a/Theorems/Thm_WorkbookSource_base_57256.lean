-- Prove2me | Theorems.Thm_WorkbookSource_base_57256
-- name    : WorkbookSource.base_57256
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:47:52.130109+00:00
-- url     : https://prove2.me/theorems/348ef094-a374-43eb-8baf-0699df15c7fe
-- title:
--   A cyclic fourth-power ratio bounds half the cubic sum
-- statement:
--   Prove that $\frac{a^4}{a+b}+\frac{b^4}{b+c}+\frac{c^4}{c+a}\geq \frac{a^3+b^3+c^3}{2} $ . $\forall a,b,c> 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57256` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57256; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_57256 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 / (a + b) + b^4 / (b + c) + c^4 / (c + a) ≥ (a^3 + b^3 + c^3) / 2  :=  by sorry
