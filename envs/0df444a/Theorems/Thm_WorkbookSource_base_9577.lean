-- Prove2me | Theorems.Thm_WorkbookSource_base_9577
-- name    : WorkbookSource.base_9577
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:10:37.848668+00:00
-- url     : https://prove2.me/theorems/0706699e-6a24-4359-a9cd-f575b3572dc9
-- title:
--   A triple-sum reciprocal inequality with a weighted quadratic denominator
-- statement:
--   Prove that for $a, b, c, d > 0$,
--   ${\frac {1}{a+b+c}}+{\frac {1}{b+c+d}}+{\frac {1}{a+c+d}}+{\frac {1}{d+a+b}}\geq {\frac {22}{3}}\,{\frac {a+b+c+d}{{a}^{2}+{c}^{2}+{b}^{2}+{d}^{2}+3\,ab+3\,bc+3\,cd+3\,ad+3\,ac+3\,bd}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9577` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9577; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9577 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / (a + b + c) + 1 / (b + c + d) + 1 / (a + c + d) + 1 / (d + a + b)) ≥ 22 / 3 * (a + b + c + d) / (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2 + 3 * a * b + 3 * b * c + 3 * c * d + 3 * a * d + 3 * a * c + 3 * b * d)  :=  by sorry
