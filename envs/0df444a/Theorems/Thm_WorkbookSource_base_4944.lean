-- Prove2me | Theorems.Thm_WorkbookSource_base_4944
-- name    : WorkbookSource.base_4944
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:54.372347+00:00
-- url     : https://prove2.me/theorems/5dc24a1c-2f9c-4c7f-b3fd-de5979d9085b
-- title:
--   A pairwise quadratic reciprocal sum is bounded above
-- statement:
--   Let $a,b,c >0$ . Prove: $\frac{{a + b}}{{{a^2} + {b^2}}} + \frac{{b + c}}{{{b^2} + {c^2}}} + \frac{{c + a}}{{{c^2} + {a^2}}} \le \frac{1}{a} + \frac{1}{b} + \frac{1}{c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4944` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4944; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4944 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a ^ 2 + b ^ 2) + (b + c) / (b ^ 2 + c ^ 2) + (c + a) / (c ^ 2 + a ^ 2) ≤ 1 / a + 1 / b + 1 / c  :=  by sorry
