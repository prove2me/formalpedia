-- Prove2me | Theorems.Thm_lean_workbook_plus_51013
-- name    : lean_workbook_plus_51013
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9ff5a2ac-e696-48f0-a62a-caf50918ade5
-- statement:
--   For those who don't know derivatives, \nuse the fact that, \n $(a+b+c)^2 \geq 3(ab+bc+ca)$ \nwhich gives, \n $\left(\tan\frac{A}{2}+\tan\frac{B}{2}+\tan\frac{C}{2}\right)^2 \geq 3(\tan\frac{A}{2}\tan\frac{B}{2}+\tan\frac{B}{2}\tan\frac{C}{2}+\tan\frac{C}{2}\tan\frac{A}{2})$ \nand \nthe well known identity, \n $\tan\frac{A}{2}\tan\frac{B}{2}+\tan\frac{B}{2}\tan\frac{C}{2}+\tan\frac{C}{2}\tan\frac{A}{2}=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51013 :
  ∀ A B C : ℝ, (A + B + C = π ∧ A > 0 ∧ B > 0 ∧ C > 0 → (Real.tan (A / 2) + Real.tan (B / 2) + Real.tan (C / 2))^2 ≥ 3 * (Real.tan (A / 2) * Real.tan (B / 2) + Real.tan (B / 2) * Real.tan (C / 2) + Real.tan (C / 2) * Real.tan (A / 2)))   :=  by sorry
