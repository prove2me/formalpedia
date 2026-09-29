-- Prove2me | Theorems.Thm_lean_workbook_plus_24949
-- name    : lean_workbook_plus_24949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/44ea100c-8f87-4bf9-8293-11701e7cfa2a
-- statement:
--   let $x=ru,y=rv,z=rw$ with $u^2+v^2+w^2=1$ in which $(u,v,w)$ represents an unitary vector meaning direction. then $x^2+y^2+z^2=r^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24949 (x y z r : ℝ) (u v w : ℝ) (h1 : u^2 + v^2 + w^2 = 1) (h2 : x = r * u) (h3 : y = r * v) (h4 : z = r * w) : x^2 + y^2 + z^2 = r^2   :=  by sorry
