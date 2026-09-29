-- Prove2me | Theorems.Thm_lean_workbook_plus_1369
-- name    : lean_workbook_plus_1369
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/9fcf552e-f158-47be-8977-180bbd2b9682
-- statement:
--   $ \frac{mz+nx}{m+n}\geq \frac{m+n}{\frac{m}{z}+\frac{n}{x}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1369 {m n z x : ℝ}
 (hm : 0 < m)
 (hn : 0 < n)
 (hz : 0 < z)
 (hx : 0 < x) :
 (m * z + n * x) / (m + n) ≥ (m + n) / (m / z + n / x)   :=  by sorry
