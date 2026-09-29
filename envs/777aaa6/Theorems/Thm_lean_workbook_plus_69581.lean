-- Prove2me | Theorems.Thm_lean_workbook_plus_69581
-- name    : lean_workbook_plus_69581
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/b4d64eba-705b-4cc9-987a-8c575f530722
-- statement:
--   Let $z_n = F_{2n+1} = \frac{a^{2n+1}-b^{2n+1}}{a-b}$ , where $a:=\frac{1+\sqrt{5}}{2}$ and $b:=\frac{1-\sqrt{5}}{2}$ . Using $a+b=1$ and $ab=-1$ , we see that the sequence $\left\{z_n\right\}_{n \in \mathbb{N}_0}$ satisfies the same recurrence relation with the same initial condition $z_0=1$ . Thus, $y_n = z_n$ for every $n \in \mathbb{N}_0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69581 :
  ∀ n : ℕ,
    ((1 + Real.sqrt 5) / 2) ^ (2 * n + 1) - ((1 - Real.sqrt 5) / 2) ^ (2 * n + 1) = fib 2*n + 1   :=  by sorry
