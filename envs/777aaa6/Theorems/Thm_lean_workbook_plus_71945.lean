-- Prove2me | Theorems.Thm_lean_workbook_plus_71945
-- name    : lean_workbook_plus_71945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b03a22e3-0789-42f9-a3e2-0ded808c7893
-- statement:
--   Simplify the complex number \(\frac{24 + 7i}{25}\) to its standard form.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71945 (z : ℂ) (h : z = (24 + 7 * Complex.I) / 25) : z = (24 / 25) + (7 / 25) * Complex.I   :=  by sorry
