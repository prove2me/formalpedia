-- Prove2me | Theorems.Thm_lean_workbook_plus_81514
-- name    : lean_workbook_plus_81514
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/72ca2bf5-1be1-45c2-ba7d-07345f1a75d4
-- statement:
--   Let $a$ , $b$ , $c$ , $d$ , and $e$ be real numbers such that $ab + bc + cd + de + ea = 1$ and $ac + bd + ce + da + eb = -3$ . Prove that $a^2 + b^2 + c^2 + d^2 + e^2 \geq 4.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81514 (a b c d e : ℝ) (h1 : a * b + b * c + c * d + d * e + e * a = 1) (h2 : a * c + b * d + c * e + d * a + e * b = -3) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 ≥ 4   :=  by sorry
