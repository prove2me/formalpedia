-- Prove2me | Theorems.Thm_lean_workbook_plus_13960
-- name    : lean_workbook_plus_13960
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/323b2d0c-5060-4e59-a1e6-1a0ec3467e8b
-- statement:
--   If $x$ is the average (arithmetic mean) of $m$ and $9$ , $y$ is the average of $2m$ and $15$ , and $z$ is the average of $3m$ and $18$ , what is the average of $x$ , $y$ , and $z$ in terms of $m$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13960 (m x y z : ℝ) (hx : x = (m + 9) / 2) (hy : y = (2 * m + 15) / 2) (hz : z = (3 * m + 18) / 2) : (x + y + z) / 3 = m + 7   :=  by sorry
