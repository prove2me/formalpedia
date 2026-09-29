-- Prove2me | Theorems.Thm_lean_workbook_plus_62003
-- name    : lean_workbook_plus_62003
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/60a1a9ef-1fd1-4810-b1b6-bc6ddfc69583
-- statement:
--   Or, if you don't want to deal with angles, note that the expression $a^2+b^2+c^2+2abc=1,\ (1)$ if treated as quadratic in $a,$ gives you: $a+bc=\sqrt{(1-b^2)(1-c^2)}.$ We get similar expressions if $(1)$ is treated as quadratic in $b$ and $c.$ Multiplying the three expressions we get $(a+bc)(b+ac)(c+ab)=(1-a^2)(1-b^2)(1-c^2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62003 :
  ∀ a b c : ℝ, a^2 + b^2 + c^2 + 2 * a * b * c = 1 → (a + b * c) * (b + a * c) * (c + a * b) = (1 - a^2) * (1 - b^2) * (1 - c^2)   :=  by sorry
