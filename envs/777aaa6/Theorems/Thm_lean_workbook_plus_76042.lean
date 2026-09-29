-- Prove2me | Theorems.Thm_lean_workbook_plus_76042
-- name    : lean_workbook_plus_76042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7a644816-9413-4281-b556-a36bc5e84018
-- statement:
--   $\frac{2}{n}>\frac{n}{n^2-n+1}\implies 2n^2-2n+2>n^2\implies n^2-2n+2>0\implies (n-1)^2+1>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76042 : ∀ n : ℕ, 2 / n > n / (n ^ 2 - n + 1) → (n - 1) ^ 2 + 1 > 0   :=  by sorry
