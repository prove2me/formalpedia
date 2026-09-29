-- Prove2me | Theorems.Thm_lean_workbook_plus_76057
-- name    : lean_workbook_plus_76057
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ecb99b21-5adc-43b8-aa1c-8238ebb952af
-- statement:
--   Evaluate the telescoping sum $\sum\limits_{k=4}^{\infty} \frac{1}{15}\left(\frac{1}{k-2}-\frac{1}{k+3}\right) -\frac{1}{3}\left(\frac{1}{k-1}-\frac{1}{k+2}\right) + \frac{2}{3}\left(\frac{1}{k}-\frac{1}{k+1}\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76057 (k : ℕ) : ∑' k : ℕ, (1/15 * (1/(k-2) - 1/(k+3)) - 1/3 * (1/(k-1) - 1/(k+2)) + 2/3 * (1/k - 1/(k+1))) = 1/6   :=  by sorry
