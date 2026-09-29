-- Prove2me | Theorems.Thm_lean_workbook_plus_73930
-- name    : lean_workbook_plus_73930
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/31c6ae3b-f8da-4466-9cdb-69c7179df84d
-- statement:
--   If $n \equiv 1 (mod 3)$ then $\frac{2n+1}{3} \in Z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73930 (n : ℤ) (hn : n ≡ 1 [ZMOD 3]) : (2 * n + 1) / 3 ∈ Set.range (Int.castRingHom ℤ)   :=  by sorry
