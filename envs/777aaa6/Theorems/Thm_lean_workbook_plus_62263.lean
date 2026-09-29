-- Prove2me | Theorems.Thm_lean_workbook_plus_62263
-- name    : lean_workbook_plus_62263
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1dc352c5-45a7-4998-bd6f-f221eac1fad8
-- statement:
--   Expanding, get: $3x^{2}yz+3y^{2}xz+3z^{2}xy\le 2x^{2}yz+2y^{2}xz+2z^{2}xy+x^{2}y^{2}+x^{2}z^{2}+y^{2}z^{2}$ $\Leftrightarrow x^{2}yz+y^{2}xz+z^{2}xy\le x^{2}y^{2}+x^{2}z^{2}+y^{2}z^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62263 (x y z : ℝ) :
  3 * x ^ 2 * y * z + 3 * y ^ 2 * x * z + 3 * z ^ 2 * x * y ≤
    2 * x ^ 2 * y * z + 2 * y ^ 2 * x * z + 2 * z ^ 2 * x * y + x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2   :=  by sorry
