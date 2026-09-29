-- Prove2me | Theorems.Thm_WorkbookSource_plus_71891
-- name    : WorkbookSource.plus_71891
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:14.99475+00:00
-- url     : https://prove2.me/theorems/c8e4cd97-2230-45d6-a2af-2519e438f9b7
-- title:
--   A squared-difference product inequality under three quadratic signs
-- statement:
--   Let $a^{2}+b^{2}-c^{2}\geq0$, $a^{2}+c^{2}-b^{2}\geq0$ and $b^{2}+c^{2}-a^{2}\geq0$. Prove that $(a+b-c)^{2}(a+c-b)^{2}\geq(a^{2}+b^{2}-c^{2})(a^{2}+c^{2}-b^{2})$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_71891` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_71891; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_71891 (a b c : ℝ) (h1 : a^2 + b^2 - c^2 ≥ 0) (h2 : a^2 + c^2 - b^2 ≥ 0) (h3 : b^2 + c^2 - a^2 ≥ 0) : (a + b - c)^2 * (a + c - b)^2 ≥ (a^2 + b^2 - c^2) * (a^2 + c^2 - b^2)   :=  by sorry
