-- Prove2me | Theorems.Thm_lean_workbook_plus_11622
-- name    : lean_workbook_plus_11622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2426bed6-30e9-40d6-8b15-ff8cbd7681e0
-- statement:
--   Let $T_k=\tfrac{k(k+1)}{2}$ be the $k$ -th triangular number. Then the given equation is equivalent to: $(T_m - T_l)^2 = (T_n - T_m) T_l.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11622 (m n l : ℕ) : (m * (m + 1) / 2 - l * (l + 1) / 2)^2 = (n * (n + 1) / 2 - m * (m + 1) / 2) * (l * (l + 1) / 2) ↔ (m * (m + 1) / 2 - l * (l + 1) / 2)^2 = (n * (n + 1) / 2 - m * (m + 1) / 2) * (l * (l + 1) / 2)   :=  by sorry
