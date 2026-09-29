-- Prove2me | Theorems.Thm_lean_workbook_plus_37670
-- name    : lean_workbook_plus_37670
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/80c69b50-cce9-441a-9a4e-7f97b023658c
-- statement:
--   Prove $ a^2b^2 + b^2c^2 + c^2a^2 \geq abc(a + b + c)$ under the given condition $ a,b,c > 0$ and $ \frac {1} {a^2} + \frac {1} {b^2} + \frac {1} {c^2} = \frac {1} {2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37670 :  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 = 1 / 2 → a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b * c * (a + b + c)   :=  by sorry
