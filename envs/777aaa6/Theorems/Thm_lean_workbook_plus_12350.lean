-- Prove2me | Theorems.Thm_lean_workbook_plus_12350
-- name    : lean_workbook_plus_12350
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/73548707-92fe-4da2-ac40-07fa1e868946
-- statement:
--   Prove for $a, b, c \in \mathbb{R^+}$\n\n$a^3c^2 + ab^4 + 2b^2c^3 \geq 4ab^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12350 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3*c^2 + a*b^4 + 2*b^2*c^3 >= 4*a*b^2*c^2   :=  by sorry
