-- Prove2me | Theorems.Thm_lean_workbook_plus_70638
-- name    : lean_workbook_plus_70638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7d6565a5-fd3d-482a-b648-c91a905011f0
-- statement:
--   If $ a \geq 0 $ , prove $ \frac{(a^{3}+b^{6})}{2} \geq 3ab^{2}-4 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70638 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a^3 + b^6) / 2 ≥ 3 * a * b^2 - 4   :=  by sorry
