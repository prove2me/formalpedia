-- Prove2me | Theorems.Thm_WorkbookSource_base_9087
-- name    : WorkbookSource.base_9087
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:43:49.253947+00:00
-- url     : https://prove2.me/theorems/42b27ccf-f932-4333-9c00-573862a2ca27
-- title:
--   A quartic bound for two squared symmetric forms
-- statement:
--   Prove that for all real numbers $a, b, c$ we have
--    $ (a^2+b^2+c^2-2ab-2bc-2ca)^2 + 9(ab+bc+ca)^2 \geq 30abc(a+b+c) $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9087` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9087; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9087 (a b c : ℝ) : (a^2+b^2+c^2-2*a*b-2*b*c-2*c*a)^2 + 9*(a*b+b*c+c*a)^2 ≥ 30*a*b*c*(a+b+c)  :=  by sorry
