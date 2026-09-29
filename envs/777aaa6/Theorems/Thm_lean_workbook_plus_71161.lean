-- Prove2me | Theorems.Thm_lean_workbook_plus_71161
-- name    : lean_workbook_plus_71161
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f696ef4f-0c39-4d6d-8155-0d8a0b4b7d56
-- statement:
--   Let $f(x,y,z)=x^3+y^3+z^3-3xyz$ . Prove the following properties:\n1. $f(x,y,z)=\frac{1}{2}\cdot(x+y+z)\cdot\left[(x-y)^2+(y-z)^2+(z-x)^2\right]$\n2. $\begin{cases}x+y+z=0\text{ or }x=y=z\iff f(x,y,z)=0\\x+y+z \ge 0\iff f(x,y,z)\ge 0\\x+y+z\le 0 \iff f(x,y,z)\le 0 \end{cases}$\n3. $\begin{cases}4\cdot f(x,y,z)=f(-x+y+z,x-y+z,x+y-z)\\2\cdot f(x,y,z)=f(x+y,y+z,z+x)\end{cases}$\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71161 :
  ∀ x y z : ℝ,
    (1 / 2) * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) =
    x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z   :=  by sorry
