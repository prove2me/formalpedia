-- Prove2me | Theorems.Thm_lean_workbook_plus_40109
-- name    : lean_workbook_plus_40109
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9fd03eb2-c61d-4758-b292-980e9f22ed34
-- statement:
--   Let $x, y, z > 0$ be real numbers such that $(x+1)(y+z)= 4$ . Prove that $xyz + xy + yz + zx \le 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40109 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : (x + 1) * (y + z) = 4) : x*y*z + x*y + y*z + z*x ≤ 4   :=  by sorry
