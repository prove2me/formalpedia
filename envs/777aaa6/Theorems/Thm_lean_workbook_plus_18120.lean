-- Prove2me | Theorems.Thm_lean_workbook_plus_18120
-- name    : lean_workbook_plus_18120
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5a331b36-feda-4708-99dd-251742e93f2c
-- statement:
--   Prove $\forall n \in N$ \n\n $\left. 7 \right|3^{2n + 1} + 2^{n + 2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18120 (n : ℕ) : 7 ∣ 3^(2 * n + 1) + 2^(n + 2)   :=  by sorry
