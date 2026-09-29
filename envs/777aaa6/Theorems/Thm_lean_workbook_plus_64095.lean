-- Prove2me | Theorems.Thm_lean_workbook_plus_64095
-- name    : lean_workbook_plus_64095
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b33fc46d-e32d-4614-b17c-e5033204f428
-- statement:
--   $x = r\cos a\cos b\cos c$ \n $y = r\cos a\cos b\sin c$ \n $z = r\sin a\cos b$ \n $u = r\sin b$ \n \n $x^2+y^2+z^2+u^2 = r^2\cos^2 a\cos^2 b\cos^2 c + r^2\cos^2 a\cos^2 b\sin^2 c + r^2\sin^2 a\cos^2 b + r^2\sin^2 b$ \n \n $= r^2\cos^2a\cos^2 b(\cos^2 c + \sin^2 c) + r^2\sin^2 a\cos^2 b + r^2\sin^2 b$ \n \n $= r^2\cos^2a\cos^2 b + r^2\sin^2 a\cos^2 b + r^2\sin^2 b$ \n \n $=r^2\cos^2 b(\cos^2a + \sin^2 a) + r^2\sin^2 b$ \n \n $=r^2\cos^2 b + r^2\sin^2 b$ \n \n $=r^2(\cos^2 b+\sin^2 b)$ \n \n $=r^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64095 (x y z u r a b c : ℝ) : 
  x = r * cos a * cos b * cos c ∧ 
  y = r * cos a * cos b * sin c ∧ 
  z = r * sin a * cos b ∧ 
  u = r * sin b → 
  x^2 + y^2 + z^2 + u^2 = r^2   :=  by sorry
