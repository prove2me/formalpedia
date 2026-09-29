-- Prove2me | Theorems.Thm_lean_workbook_plus_812
-- name    : lean_workbook_plus_812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/bf841128-c5d7-458e-a6bc-9d05436e6aee
-- statement:
--   By Cauchy-Schwarz, $(1^2 +1^2+1^2)(i^2+j^2+k^2)\ge(i+j+k)^2\Longleftrightarrow -\sqrt{3\times 2011} \le i+j+k\le \sqrt{3\times 2011}$ . Since they are integers, $\lfloor\sqrt{3\times 2011}\rfloor=77$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_812  (i j k : ℤ)
  (h₀ : 0 < i ∧ 0 < j ∧ 0 < k)
  (h₁ : i^2 + j^2 + k^2 = 2011)
  (h₂ : i + j + k = 0) :
  - Real.sqrt (3 * 2011) ≤ i + j + k ∧ i + j + k ≤ Real.sqrt (3 * 2011)   :=  by sorry
