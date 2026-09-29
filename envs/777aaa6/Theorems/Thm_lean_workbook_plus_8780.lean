-- Prove2me | Theorems.Thm_lean_workbook_plus_8780
-- name    : lean_workbook_plus_8780
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/46487f27-2ddd-47ef-91ff-518b20b1c9b8
-- statement:
--   Prove that for $x = a + b; y = b + c; z = c + a$ and $a, b, c > 0$, $a^3 +b^3 +c^3 +a^2 b +b^2 c+c^2 a \geq 2(ab^2 +bc^2 +ca^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8780 (x y z a b c : ℝ) (hx : x = a + b) (hy : y = b + c) (hz : z = c + a) (hab : a > 0 ∧ b > 0 ∧ c > 0) : a^3 + b^3 + c^3 + a^2 * b + b^2 * c + c^2 * a >= 2 * (a * b^2 + b * c^2 + c * a^2)   :=  by sorry
