-- Prove2me | Theorems.Thm_lean_workbook_plus_19043
-- name    : lean_workbook_plus_19043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a8953f6f-7b88-46cb-9d83-cecbfd38c013
-- statement:
--   prove that for all real numbers $a$, $b$, $c$, and $d$, \(\sqrt{(a^{2}+b^{2})(c^{2}+d^{2})}\geq (ad+bc)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19043 (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c   :=  by sorry
