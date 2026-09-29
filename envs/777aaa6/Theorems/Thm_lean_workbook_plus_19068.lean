-- Prove2me | Theorems.Thm_lean_workbook_plus_19068
-- name    : lean_workbook_plus_19068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f9241241-d571-4960-9f2b-6a52a080f899
-- statement:
--   $ \frac{my+nz}{m+n}\geq \frac{m+n}{\frac{m}{y}+\frac{n}{z}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19068 {m n y z : ℝ} (hm : 0 < m) (hn : 0 < n) (hy : 0 < y) (hz : 0 < z) :
  (m * y + n * z) / (m + n) ≥ (m + n) / (m / y + n / z)   :=  by sorry
