-- Prove2me | Theorems.Thm_lean_workbook_plus_80460
-- name    : lean_workbook_plus_80460
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5b489fe7-e328-48b5-91dd-a414e9d286e3
-- statement:
--   Let $n = p_1^{\alpha_1}...p_k^{\alpha_k}$ . We know that $\phi(n) = p_1^{\alpha_1-1}...p_k^{\alpha_k-1}(p_1-1)...(p_k-1)$ and notice that $2 \mid \phi(n)$ for all $n \geq 3$ because either there exists an odd prime dividing $n$ in which case $2 \mid p-1 \mid n$ or $v_2(n) \geq 2$ in which case $2 \mid \phi(n)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80460 (n : ℕ) (hn : 3 ≤ n) : 2 ∣ φ n   :=  by sorry
