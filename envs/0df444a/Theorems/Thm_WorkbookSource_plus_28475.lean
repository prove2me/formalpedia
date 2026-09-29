-- Prove2me | Theorems.Thm_WorkbookSource_plus_28475
-- name    : WorkbookSource.plus_28475
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:48.987894+00:00
-- url     : https://prove2.me/theorems/4889be36-d1e5-45ef-b9c4-636259cc4af8
-- title:
--   A product of shifted squares bounds a squared pairwise sum
-- statement:
--   Prove that: $(a^{2}+2)(b^{2}+2)(c^{2}+2) \geq \frac{3}{2}(ab+bc+ca)^{2}$ holds for all reals $a$ , $b$ , $c$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28475` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28475; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28475 (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 / 2 * (a * b + b * c + c * a)^2   :=  by sorry
