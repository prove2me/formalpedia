-- Prove2me | Theorems.Thm_lean_workbook_plus_40739
-- name    : lean_workbook_plus_40739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9561732c-db41-44b8-80c9-5520af5dcf07
-- statement:
--   Let a,b,c,d positive reals, so that $a+b+c+d=1$ . Proof that $ab+ac+ad+bc+bd+cd\leq \frac{3}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40739 (a b c d : ℝ) (h : a + b + c + d = 1) : a * b + a * c + a * d + b * c + b * d + c * d ≤ 3 / 8   :=  by sorry
