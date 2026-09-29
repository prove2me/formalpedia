-- Prove2me | Theorems.Thm_lean_workbook_plus_11021
-- name    : lean_workbook_plus_11021
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4469d731-2a94-4cbd-82a6-e1714cbd7b6f
-- statement:
--   $\Rightarrow 4q \geqslant 4 \left(\frac{36p+72-p^3}{63-4p} \right) \geqslant p+9 \Leftrightarrow \left(p-3 \right) \left(4p^2 + 8p - 93 \right) \leqslant 0, \ \text{true for all} \ 3 \leqslant p < \frac{31}{9}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11021 (p : ℝ) (hp : 3 ≤ p ∧ p < 31 / 9) (q : ℝ) (hq : q = (36 * p + 72 - p ^ 3) / (63 - 4 * p)) : p + 9 ≤ 4 * q   :=  by sorry
