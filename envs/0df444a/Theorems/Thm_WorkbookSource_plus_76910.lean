-- Prove2me | Theorems.Thm_WorkbookSource_plus_76910
-- name    : WorkbookSource.plus_76910
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:54.324579+00:00
-- url     : https://prove2.me/theorems/6ea89af1-5dff-4b0c-9b38-0866a203bf95
-- title:
--   A fourth-power and pairwise-product lower bound
-- statement:
--   Prove that $a^4+b^4+c^4+8(ab+bc+ca) \geq 27$ for real positive numbers $a, b, c$ with $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76910` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76910; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76910 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^4 + b^4 + c^4 + 8 * (a * b + b * c + c * a) ≥ 27   :=  by sorry
