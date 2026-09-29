-- Prove2me | Theorems.Thm_lean_workbook_plus_77409
-- name    : lean_workbook_plus_77409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f114ab1b-d7e5-4514-b69f-6d4d70c9d659
-- statement:
--   Let $ S_n = 4^{n+1} + 5^{2n-1}$ . If $ 21 | S_k = 4^{k+1} + 5^{2k-1}$ , then \n\n $ S_{k+1} = 4^{k+2} + 5^{2k+1} = 4 \cdot 4^{k+1} + 25 \cdot 5^{2k-1} = 4S_k + 21 \cdot 5^{2k-1}$ \n\n so $ 21 | S_{k+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77409  (n : ℕ)
  (h₀ : 21 ∣ (4^(n + 1) + 5^(2 * n - 1))) :
  21 ∣ (4^(n + 2) + 5^(2 * n + 1))   :=  by sorry
