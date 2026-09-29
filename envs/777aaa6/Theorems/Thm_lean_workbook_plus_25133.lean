-- Prove2me | Theorems.Thm_lean_workbook_plus_25133
-- name    : lean_workbook_plus_25133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/43577065-17e2-499c-91c1-175e3745bac4
-- statement:
--   Given a sequence $w_{0}, w_{1}, w_{2}, ..., $ the sequence $F_{1}, F_{2}, ...$ is defined by $F_{n}= w_{n}^{2} + w_{n-1}^{2} - 4w_{n}w_{n-1}$ . Show that $F_{n} - F_{n-1} = (w_{n} - w_{n-2})(w_{n} + w_{n-2} -4w_{n-1})$ for $n \geq 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25133 (w : ℕ → ℝ) (F : ℕ → ℝ) (h₁ : ∀ n, F n = (w n)^2 + (w (n-1))^2 - 4 * w n * w (n-1)) (h₂ : ∀ n, n ≥ 2 → F n - F (n-1) = (w n - w (n-2)) * (w n + w (n-2) - 4 * w (n-1))) : ∀ n, n ≥ 2 → F n - F (n-1) = (w n - w (n-2)) * (w n + w (n-2) - 4 * w (n-1))   :=  by sorry
