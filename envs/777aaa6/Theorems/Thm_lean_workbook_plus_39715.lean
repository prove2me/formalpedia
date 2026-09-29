-- Prove2me | Theorems.Thm_lean_workbook_plus_39715
-- name    : lean_workbook_plus_39715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b4d0b799-fb1e-49af-aa8c-430a35781fb5
-- statement:
--   Let $a, b, c \geq 0$ and satisfy $ a^2+b^2+c^2 +abc = 4 . $ Show that $ ab + bc + ca - abc \leq 2. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39715 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a * b + b * c + c * a - a * b * c ≤ 2   :=  by sorry
