-- Prove2me | Theorems.Thm_lean_workbook_plus_11513
-- name    : lean_workbook_plus_11513
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4ad1d598-3032-4026-9262-61909975597a
-- statement:
--   Let $a, b, c, d, e$ be positive real numbers such that $abcde = 1$ . Prove that \n $$\sum\limits_{cyc} \frac{a + abc}{1 + ab + abcd} \ge \frac{10}{3}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11513 (hx: a * b * c * d * e = 1) : (a + a * b * c) / (1 + a * b + a * b * c * d) + (b + b * c * d) / (1 + b * c + b * c * d * e) + (c + c * d * e) / (1 + c * d + c * d * e * a) + (d + d * e * a) / (1 + d * e + d * e * a * b) + (e + e * a * b) / (1 + e * a + e * a * b * c) ≥ 10 / 3   :=  by sorry
