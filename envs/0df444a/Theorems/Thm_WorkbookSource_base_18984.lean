-- Prove2me | Theorems.Thm_WorkbookSource_base_18984
-- name    : WorkbookSource.base_18984
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:49.087759+00:00
-- url     : https://prove2.me/theorems/c559310f-c772-43b3-bc7b-d90ee50d4c64
-- title:
--   A cubic symmetric ratio bounded by pairwise rational terms
-- statement:
--   THQ023. Let $a, \, b, \, c \, > \, 0$ . Prove that $ {\frac {{a}^{2}}{b+c}}+{\frac {{b}^{2}}{a+c}}+{\frac {{c}^{2}}{a+b}}+{\frac {3(ba+bc+ac)}{2(a+b+c)}}\ge{\frac { \left( a+b+c \right) ^{3}}{3(ab+bc+ca)}} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18984` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18984; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18984 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (a + c) + c^2 / (a + b) + (3 * (a * b + b * c + a * c)) / (2 * (a + b + c))) ≥ (a + b + c)^3 / (3 * (a * b + b * c + a * c))  :=  by sorry
