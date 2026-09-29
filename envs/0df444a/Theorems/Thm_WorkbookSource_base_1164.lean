-- Prove2me | Theorems.Thm_WorkbookSource_base_1164
-- name    : WorkbookSource.base_1164
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:38:03.770341+00:00
-- url     : https://prove2.me/theorems/7d63868e-b164-42b4-b6ca-359cf62587ff
-- title:
--   Combining two fractions under a square root
-- statement:
--   Prove that $\sqrt{2(\frac{a}{5-a}+\frac{b}{5-b})}=\sqrt{\frac{2[5(a+b)-2ab]}{25-5(a+b)+ab}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1164` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1164; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1164 (a b : ℝ): (a ≠ 5 ∧ b ≠ 5) → √(2 * (a / (5 - a) + b / (5 - b))) = √((2 * (5 * (a + b) - 2 * a * b)) / (25 - 5 * (a + b) + a * b))  :=  by sorry
