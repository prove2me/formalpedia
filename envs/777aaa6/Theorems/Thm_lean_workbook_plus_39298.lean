-- Prove2me | Theorems.Thm_lean_workbook_plus_39298
-- name    : lean_workbook_plus_39298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/996a7f52-0287-42e2-b327-584bfc217544
-- statement:
--   Prove that for positive integers $x$ , $y$ , and $z$ that $x+xy+z^3>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39298 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x + x*y + z^3 > 0   :=  by sorry
