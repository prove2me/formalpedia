-- Prove2me | Theorems.Thm_lean_workbook_plus_4777
-- name    : lean_workbook_plus_4777
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9da58c0a-4404-4024-8f8c-50038a9ab84f
-- statement:
--   Then, $a^{2}b^{2}c^{2}(a^{2}+b^{2})(b^{2}+c^{2})(c^{2}+a^{2}) \le \frac{1}{2^{9}}(a+b)^{4}(b+c)^{4}(c+a)^{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4777 : ∀ a b c : ℝ, a^2 * b^2 * c^2 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≤ (1 / (2^9)) * (a + b)^4 * (b + c)^4 * (c + a)^4   :=  by sorry
