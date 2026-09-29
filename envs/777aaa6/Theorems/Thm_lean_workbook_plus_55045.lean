-- Prove2me | Theorems.Thm_lean_workbook_plus_55045
-- name    : lean_workbook_plus_55045
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4fb83099-a076-4787-8285-2ed8a999ecec
-- statement:
--   prove that \\(0\leq \\frac {a \left( b+c \right) }{x \left( y+z \right) }+\\frac {b \left( c+a \right) }{y \left( z+x \right) }+\\frac {c \left( a+b \right) }{z \left( x+y \right) }-\\frac {a}{x}-\\frac {b}{y}-\\frac {c}{z}\\) given \\(a \geq x,b \geq y,c \geq z\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55045 :  ∀ a b c x y z : ℝ, a ≥ x ∧ b ≥ y ∧ c ≥ z → 0 ≤ a * (b + c) / (x * (y + z)) + b * (c + a) / (y * (z + x)) + c * (a + b) / (z * (x + y)) - a / x - b / y - c / z   :=  by sorry
