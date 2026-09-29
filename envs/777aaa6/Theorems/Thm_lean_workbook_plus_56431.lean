-- Prove2me | Theorems.Thm_lean_workbook_plus_56431
-- name    : lean_workbook_plus_56431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ec7ac709-e7c3-4990-bee5-cd4e0ec59a9a
-- statement:
--   From $ x\geq y\geq z$ , we have $ (x-y)(y-z)\geq 0\Rightarrow xy+yz\geq y^2+xz\Rightarrow xz\leq \frac{1-y^2}{2}$ . This proves $ xz\leq \frac{1}{2}$ . If we had equality, then $ xz\leq \frac{1-y^2}{2}$ would imply $ y=0$ . But then plug into the original $ xy+yz+zx=1$ to get $ \frac{1}{2}=1$ , a contradiction. So the inequality is strict.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56431  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x ≥ y ∧ y ≥ z)
  (h₂ : x * y + y * z + z * x = 1) :
  x * z ≤ 1 / 2   :=  by sorry
