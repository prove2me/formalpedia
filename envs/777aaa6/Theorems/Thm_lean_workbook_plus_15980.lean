-- Prove2me | Theorems.Thm_lean_workbook_plus_15980
-- name    : lean_workbook_plus_15980
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6a89e087-f008-4d7a-9ac5-199f54092899
-- statement:
--   For $a, b ,c > 0 $ real numbers:\n\n $ a^2+b^2+c^2 \ge \frac{a^3+b^3+c^3}{a+b+c} + \frac{2}{3} (ab+bc+ca) \ \ ; $\n\nGreetings!\n\nNice and easy inequalities!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15980 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 ≥ (a^3 + b^3 + c^3) / (a + b + c) + (2 / 3) * (a * b + b * c + c * a)   :=  by sorry
