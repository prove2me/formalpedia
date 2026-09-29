-- Prove2me | Theorems.Thm_lean_workbook_plus_37765
-- name    : lean_workbook_plus_37765
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5e9d537f-a6e0-4d83-a910-1a90ae97ee1f
-- statement:
--   Given a quartet of positive numbers $a,b,c,d$ , and is known, that $abcd=1$ . Prove that $a^2+b^2+c^2+d^2+ab+ac+ad+bc+bd+dc \ge 10$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37765 : a * b * c * d = 1 → a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + a * b + a * c + a * d + b * c + b * d + c * d ≥ 10   :=  by sorry
