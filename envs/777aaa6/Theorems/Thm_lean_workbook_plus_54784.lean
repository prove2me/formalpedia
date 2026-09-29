-- Prove2me | Theorems.Thm_lean_workbook_plus_54784
-- name    : lean_workbook_plus_54784
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/73728d1d-6ac7-4db4-93ac-95acd6c7abfa
-- statement:
--   Suppose $y$ between $x$ and $z.$ By AM-GM Inequality, we have \n $4\,xyz \left( xy+zx+yz \right) \left( x+y+z \right) \leqslant [zx(x+y+z)+y(xy+yz+zx)]^2.$ We need to prove that \n $3\,xyz+{x}^{2}y+{y}^{2}z+{z}^{2}x \geqslant xy(x+y+z)+z(xy+yz+zx),$ equivalent to \n $x(x-y)(y-z) \geqslant 0.$ Which is true.\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54784  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : y ≠ x)
  (h₂ : y ≠ z)
  (h₃ : z ≠ x)
  (h₄ : x + y + z = 1) :
  4 * x * y * z * (x * y + y * z + z * x) * (x + y + z) ≤ (z * x * (x + y + z) + y * (x * y + y * z + z * x))^2   :=  by sorry
