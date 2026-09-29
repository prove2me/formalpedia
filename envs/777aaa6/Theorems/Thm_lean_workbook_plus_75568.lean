-- Prove2me | Theorems.Thm_lean_workbook_plus_75568
-- name    : lean_workbook_plus_75568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ab7886b3-64cb-49a2-a43c-f3c1bb54ba3a
-- statement:
--   Let $a, b, c > 0$ satisfy $a + b + c \ge \frac{1}{a} +\frac{1}{b} +\frac{1}{c}$ . Prove that $a^3 + b^3 + c^3 \ge a + b + c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75568 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a + b + c ≥ 1/a + 1/b + 1/c → a^3 + b^3 + c^3 ≥ a + b + c   :=  by sorry
