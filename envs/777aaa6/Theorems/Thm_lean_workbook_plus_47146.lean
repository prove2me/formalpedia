-- Prove2me | Theorems.Thm_lean_workbook_plus_47146
-- name    : lean_workbook_plus_47146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/6cba1b4d-810e-4997-8c06-317cb04f9b34
-- statement:
--   $\Leftrightarrow \left (\frac{1}{\sqrt[4]{ac}}-\sqrt[4]{ac}\right)^2+(\sqrt{a}-\sqrt{c})^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47146 : ∀ a c : ℝ, (1 / (a * c)^(1 / 4) - (a * c)^(1 / 4))^2 + (Real.sqrt a - Real.sqrt c)^2 ≥ 0   :=  by sorry
