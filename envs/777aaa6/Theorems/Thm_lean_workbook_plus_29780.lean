-- Prove2me | Theorems.Thm_lean_workbook_plus_29780
-- name    : lean_workbook_plus_29780
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/08cd3425-9aa7-4e49-9fdf-3a6a4b6e246a
-- statement:
--   Prove that: $\forall \mathop {}\limits^{} z \in C\mathop {}\limits^{} ,\mathop {}\limits^{} {\mathop{\rm Re}\nolimits} (z) < - \frac{1}{2}\mathop {}\limits^{} \Rightarrow \mathop {}\limits^{} \left| {1 + {z^2}} \right| > \left| {1 + z + {z^2}} \right|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29780 (z : ℂ) (h : z.re < -1 / 2) : ‖(1 + z^2)‖ > ‖(1 + z + z^2)‖   :=  by sorry
