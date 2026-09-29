-- Prove2me | Theorems.Thm_lean_workbook_plus_59348
-- name    : lean_workbook_plus_59348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5f1855d9-0bed-4c19-a2d9-f3920bd48347
-- statement:
--   SolutionIf $x$ is the number of purple socks that Jamal added, then $$\frac{18+x}{6+18+12+x}=\frac{18+x}{36+x}=\frac{3}{5} \implies 90+5x=108+3x \implies x=\frac{108-90}{5-3}=\boxed{\textbf{(B)}}~9.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59348  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (18 + x) / (6 + 18 + 12 + x) = 3 / 5) :
  x = 9   :=  by sorry
