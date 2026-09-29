-- Prove2me | Theorems.Thm_lean_workbook_plus_35917
-- name    : lean_workbook_plus_35917
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/69bfb323-e7c9-4b16-bd68-1c77211e7aa7
-- statement:
--   Prove that $2h(x) = f(x) + g(x) - |f(x) - g(x)|$ is continuous and has a primitive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35917 (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => 2 * (f x + g x - |f x - g x|))   :=  by sorry
