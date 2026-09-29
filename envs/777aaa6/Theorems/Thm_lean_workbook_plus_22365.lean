-- Prove2me | Theorems.Thm_lean_workbook_plus_22365
-- name    : lean_workbook_plus_22365
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/fb1c3bc6-0cd4-474f-8569-b6fb6d5ebddc
-- statement:
--   From Moldova TST $ 2005 $ : $ a^3b^2+b^3c^2+c^3a^2\ge abc(a^2+b^2+c^2) $ and IMO $ 1983 $ : $ a^3b+b^3c+c^3a \ge a^2b^2+b^2c^2+c^2a^2 $ we also have a nice inequality: \n\n $ \frac{a^3(a+b)}{a^2+b^2}+\frac{b^3(b+c)}{b^2+c^2}+\frac{c^3(c+a)}{c^2+a^2} \ge a^2+b^2+c^2 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22365 : ∀ a b c : ℝ, (a^3 * (a + b) / (a^2 + b^2) + b^3 * (b + c) / (b^2 + c^2) + c^3 * (c + a) / (c^2 + a^2)) ≥ a^2 + b^2 + c^2   :=  by sorry
