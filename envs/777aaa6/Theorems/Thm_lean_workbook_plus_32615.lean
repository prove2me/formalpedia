-- Prove2me | Theorems.Thm_lean_workbook_plus_32615
-- name    : lean_workbook_plus_32615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/bb27f718-2ff3-4aa8-929b-d279892ec077
-- statement:
--   Let $x+y+z=a, \frac 1 x + \frac 1 y + \frac 1 z = b, xyz =c$ , where $a,b,c$ are positive integers. Then $xy+yz+zx = bc$ is an integer too. It follows that $x,y,z$ are roots of the polynomial $P(t)=t^3 - at^2 + bct - c$ , which is normalized and has integer coefficients. It is well-known that any root of such a polynomial is either an integer or an irrational number. Since $x,y,z$ are supposed to be rational, it follows that they are integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32615  (x y z a b c : ℚ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : x + y + z = a)
  (h₂ : 1 / x + 1 / y + 1 / z = b)
  (h₃ : x * y * z = c)
  (h₄ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x * y + y * z + z * x = b * c   :=  by sorry
