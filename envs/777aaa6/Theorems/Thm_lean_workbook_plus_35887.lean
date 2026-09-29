-- Prove2me | Theorems.Thm_lean_workbook_plus_35887
-- name    : lean_workbook_plus_35887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1cf94d80-dc59-4778-bca8-7074d5cf9784
-- statement:
--   Show that $(a^3+b^3+c^3-3abc)(x^3+y^3+z^3-3xyz) = A^3+B^3+C^3-3ABC$, where $A=ax+by+cz, B=ay+bz+cx, C=az+bx+cy$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35887 {a b c x y z A B C : ℂ} (ha : A = a * x + b * y + c * z) (hb : B = a * y + b * z + c * x) (hc : C = a * z + b * x + c * y) : (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z) = A ^ 3 + B ^ 3 + C ^ 3 - 3 * A * B * C   :=  by sorry
