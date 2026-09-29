-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_11171
-- name    : WorkbookCorrected.plus_11171
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:13:52.978171+00:00
-- url     : https://prove2.me/theorems/8f43b21e-74c5-46ca-a2b8-926b5678d521
-- title:
--   The floor of a telescoping sum along a quadratic recurrence
-- statement:
--   Let the sequence $x_{1} = \frac{1}{2}$ and $x_{k+1} = x^2_{k} + x_{k}$ and $:$\n$A = \frac{1}{x_{1} + 1} + \frac{1}{x_{2} + 1} + \cdots + \frac{1}{x_{100} + 1}$\nDetermine $\lfloor{A} \rfloor$
--
--   The required floor is1.
--
--   Formalization Note: The original formalization summed indices0 through99 and imposed the recurrence at0. This correction restores the source indices1 through100 and the recurrence for k≥1.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_11171 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11171; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_11171 (x : ℕ → ℝ) (h0 : x 1=1/2)
    (h : ∀ k : ℕ, 1≤k → x (k+1)=(x k)^2+x k) :
    ⌊∑ k ∈ Finset.range 100, (1/(x (k+1)+1))⌋ = (1:ℤ) := by sorry
