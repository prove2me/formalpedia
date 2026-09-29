-- Prove2me | Theorems.Thm_lean_workbook_plus_55728
-- name    : lean_workbook_plus_55728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d0e94f5b-065a-42e9-a630-a882498127c4
-- statement:
--   Let $a,b,c >0$ and $a^2+b^2+c^2 +3= 2(ab+bc+ca).$ Prove that $a^2+2bc\geq3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55728 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 3 = 2 * (a * b + b * c + c * a)) : a^2 + 2 * b * c ≥ 3   :=  by sorry
