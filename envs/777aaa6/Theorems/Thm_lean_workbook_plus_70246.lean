-- Prove2me | Theorems.Thm_lean_workbook_plus_70246
-- name    : lean_workbook_plus_70246
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/30ef2807-eb61-4d5e-ae65-ec564053e514
-- statement:
--   Prove that $\sum_{k=1}^{p-1} \frac{1}{k(p-k)} \equiv -\sum_{k=1}^{p-1} (k^{-1})^2 \equiv -\sum_{j=1}^{p-1} j^2 \equiv 0 (\text{mod} p)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70246 (p : ℕ) (hp : p.Prime) : (∑ k in Finset.Ico 1 (p-1), (1 : ℤ)/(k*(p-k))) ≡ 0 [ZMOD p]   :=  by sorry
