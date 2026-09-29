-- Prove2me | Theorems.Thm_lean_workbook_plus_81968
-- name    : lean_workbook_plus_81968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/206b8280-7eef-4229-804c-0761575fc726
-- statement:
--   The real numbers $a,b$ and $c$ satisfy the inequalities $|a|\ge |b+c|,|b|\ge |c+a|$ and $|c|\ge |a+b|$ . Prove that $a+b+c=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81968 (a b c : ℝ) (h1 : |a| ≥ |b + c|) (h2 : |b| ≥ |c + a|) (h3 : |c| ≥ |a + b|) : a + b + c = 0   :=  by sorry
