-- Prove2me | Theorems.Thm_lean_workbook_plus_6409
-- name    : lean_workbook_plus_6409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/846e9720-5185-4674-b386-678c93aca98d
-- statement:
--   Prove that $n(n^2+5)$ is divisible by $6$, $n\in\mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6409 : ∀ n : ℕ, 6 ∣ n * (n^2 + 5)   :=  by sorry
