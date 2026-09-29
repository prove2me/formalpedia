-- Prove2me | Theorems.Thm_lean_workbook_plus_77961
-- name    : lean_workbook_plus_77961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8a2a105b-eed7-436c-afb8-da5711c31a94
-- statement:
--   Let numbers are $a, a+1,a+2$. \nthen: $a^3+(a+1)^3+(a+2)^3=3a^3+9a^2+15a+9$ \nThen: $3a+3|3a^3+9a^2+15a+9$ \nthen: $(3a+3).(a^2+2a+3)=3a^3+9a^2+15a+9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77961 : ∀ a : ℤ, a^3 + (a + 1)^3 + (a + 2)^3 = 3 * a^3 + 9 * a^2 + 15 * a + 9 ∧ 3 * a + 3 ∣ 3 * a^3 + 9 * a^2 + 15 * a + 9 ∧ (3 * a + 3) * (a^2 + 2 * a + 3) = 3 * a^3 + 9 * a^2 + 15 * a + 9 ∧ a^2 + 2 * a + 3 = a^2 + 2 * a + 3 ∧ (3 * a + 3) * (a^2 + 2 * a + 3) = 3 * a^3 + 9 * a^2 + 15 * a + 9   :=  by sorry
