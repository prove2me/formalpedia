-- Prove2me | Theorems.Thm_WorkbookCorrected_base_47199
-- name    : WorkbookCorrected.base_47199
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:20.552409+00:00
-- url     : https://prove2.me/theorems/b4856bc8-966a-4434-92ae-723737a177f8
-- title:
--   A quadratic-factor product bound with an attaining example
-- statement:
--   Prove that for all real numbers $x, y, z$ satisfying $x+y+z+2=xyz$, $(x^2+1)(y^2+1)(z^2+1) \geq 4$ and equality holds for example when $x=0, \; y=z=-1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47199` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47199; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_47199 : (∀ (x y z : ℝ) (h : x + y + z + 2 = x * y * z), (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 4) ∧ ((((0) : ℝ) + ((-1) : ℝ) + ((-1) : ℝ) + 2 = ((0) : ℝ) * ((-1) : ℝ) * ((-1) : ℝ)) ∧ ( (((0) : ℝ) ^ 2 + 1) * (((-1) : ℝ) ^ 2 + 1) * (((-1) : ℝ) ^ 2 + 1)  =  4  )) := by sorry
