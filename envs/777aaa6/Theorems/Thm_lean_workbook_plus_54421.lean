-- Prove2me | Theorems.Thm_lean_workbook_plus_54421
-- name    : lean_workbook_plus_54421
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/229c561d-5894-42be-8f99-e8ecbb005aeb
-- statement:
--   Let $a,b,c >0$ and $a^2+b^2+c^2 =\frac{3}{2}(ab+bc+ca-1)$ . Prove that $abc \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54421 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : a^2 + b^2 + c^2 = (3 / 2) * (a * b + b * c + c * a - 1) → a * b * c ≥ 1   :=  by sorry
