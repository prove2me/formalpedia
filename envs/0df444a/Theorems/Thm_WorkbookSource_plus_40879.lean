-- Prove2me | Theorems.Thm_WorkbookSource_plus_40879
-- name    : WorkbookSource.plus_40879
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:34:56.024677+00:00
-- url     : https://prove2.me/theorems/ea27b719-5c76-4419-a764-68b42897ea45
-- title:
--   A squared cubic sum bounds a pairwise sum times a fourth power
-- statement:
--   For $a,b,c\geq 0$ then $(ab+ac+bc)(a+b+c)^4\leq 27(a^3+b^3+c^3)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_40879` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40879; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_40879 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a * b + a * c + b * c) * (a + b + c) ^ 4 ≤ 27 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2   :=  by sorry
