-- Prove2me | Theorems.Thm_lean_workbook_plus_7110
-- name    : lean_workbook_plus_7110
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/9361fa02-ad1e-470f-a46b-78b6c8eacc80
-- statement:
--   $ \frac{mx+ny}{m+n}\geq \frac{m+n}{\frac{m}{x}+\frac{n}{y}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7110 {m n x y : ℝ} (hm : 0 < m) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
  (m * x + n * y) / (m + n) ≥ (m + n) / (m / x + n / y)   :=  by sorry
