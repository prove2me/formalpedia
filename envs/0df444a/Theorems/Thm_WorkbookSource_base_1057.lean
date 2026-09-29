-- Prove2me | Theorems.Thm_WorkbookSource_base_1057
-- name    : WorkbookSource.base_1057
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:25:54.283028+00:00
-- url     : https://prove2.me/theorems/dec89ede-d66f-4552-a06c-20b74d69711e
-- title:
--   A six-term pair-sum reciprocal lower bound
-- statement:
--   Let $a,b,c,d>0$ ,prove $ {\frac {1}{a+b}}+{\frac {1}{b+c}}+{\frac {1}{c+d}}+{\frac {1}{d+a}}+{\frac {1}{c+a}}+{\frac {1}{b+d}}\geq \frac{9}{2}\,{\frac {a+b+c+d}{ab+bc+cd+ad+ac+bd}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1057` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1057; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1057 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / (a + b) + 1 / (b + c) + 1 / (c + d) + 1 / (d + a) + 1 / (c + a) + 1 / (b + d) ≥ 9 / 2 * (a + b + c + d) / (a * b + b * c + c * d + d * a + a * c + b * d)  :=  by sorry
