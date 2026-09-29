-- Prove2me | Theorems.Thm_lean_workbook_plus_79740
-- name    : lean_workbook_plus_79740
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1868b720-6840-40fc-a442-c718fd758cf4
-- statement:
--   Find $\lim\limits_{x\to 0}\frac{\tan{2x}-2\sin{x}}{x(1-\cos{2x})}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79740 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |(tan 2*x - 2*sin x) / (x*(1 - cos 2*x)) - 3/2| < ε   :=  by sorry
