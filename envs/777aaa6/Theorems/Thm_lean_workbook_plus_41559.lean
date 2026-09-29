-- Prove2me | Theorems.Thm_lean_workbook_plus_41559
-- name    : lean_workbook_plus_41559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/619c5a45-5602-4a5d-b45c-fd719848ed8d
-- statement:
--   Prove that $ \forall n \in N$ : $ 10^n| \left\lfloor (5+\sqrt{35})^{2n-1} \right\rfloor$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41559 : ∀ n : ℕ, 10 ^ n ∣ (5 + Real.sqrt 35)^(2 * n - 1)   :=  by sorry
