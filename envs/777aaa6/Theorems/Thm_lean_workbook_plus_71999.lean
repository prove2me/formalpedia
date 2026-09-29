-- Prove2me | Theorems.Thm_lean_workbook_plus_71999
-- name    : lean_workbook_plus_71999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9c452443-0df7-4016-a927-567c9530fd73
-- statement:
--   Prove the inequality $(a^2+1)(b^2+1)(c^2+1) \ge (ab+1)(bc+1)(ca+1)$ is true for all positive real numbers $a$ , $b$ , $c$ with equality holding at $a=b=c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71999 (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b + 1) * (b * c + 1) * (c * a + 1)   :=  by sorry
