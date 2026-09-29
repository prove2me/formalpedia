-- Prove2me | Theorems.Thm_lean_workbook_plus_3566
-- name    : lean_workbook_plus_3566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/afe49705-502e-4d7b-911d-ec4ac0aae3b2
-- statement:
--   A cup of boiling water ($212^{\circ}\text{F}$) is placed to cool in a room whose temperature remains constant at $68^{\circ}\text{F}$. Suppose the difference between the water temperature and the room temperature is halved every $5$ minutes. What is the water temperature, in degrees Fahrenheit, after $15$ minutes?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3566 (T : ℕ → ℝ) (h₁ : T 0 = 212) (h₂ : ∀ n, T (n + 5) = (T n + 68) / 2) : T 15 = 86   :=  by sorry
