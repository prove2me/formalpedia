-- Prove2me | Theorems.Thm_lean_workbook_plus_8898
-- name    : lean_workbook_plus_8898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/616c1eda-b39e-445c-acdb-e65fdfc3988d
-- statement:
--   $\sum_{cyc}\frac{2-a}{2+a}\geq\frac{15}{7} \Leftrightarrow$ $\sum_{cyc}\frac{4}{2+a}\geq\frac{36}{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8898 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 - a) / (2 + a) + (2 - b) / (2 + b) + (2 - c) / (2 + c) ≥ 15 / 7 ↔ 4 / (2 + a) + 4 / (2 + b) + 4 / (2 + c) ≥ 36 / 7   :=  by sorry
